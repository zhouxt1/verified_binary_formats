#!/usr/bin/env python3
"""Rough Verus line counts: spec (spec fns, and requires/ensures/invariant/
decreases clauses), proof (proof fns, proof blocks, asserts), exec (the rest
of the code), comments/blank excluded. Heuristic, by brace tracking."""
import re,sys,os
DEBUG=os.environ.get("DBG")
def count(path):
    L=open(path).read().split('\n')
    c={'spec':0,'proof':0,'exec':0}
    stack=[]  # kinds of open brace regions
    mode=None # pending kind for next '{'
    clause=False
    for raw in L:
        line=raw.strip()
        if not line or line.startswith('//'): continue
        cur = stack[-1] if stack else 'exec'
        # function headers
        m=re.match(r'(pub(\([a-z]+\))? )?(open |closed )?(spec|proof)? ?fn ',line)
        if re.search(r'\b(spec) fn\b',line): mode='spec'
        elif re.search(r'\bproof fn\b',line): mode='proof'
        elif re.search(r'\bfn\b',line) and cur=='exec': mode='exec'
        kind=cur
        if mode: kind=mode
        if re.match(r'(requires|ensures|invariant|decreases|recommends)\b',line): clause=True
        if clause and cur=='exec' and not mode in ('spec','proof'): kind='spec'
        if re.match(r'(proof|assert|assert forall|reveal|lemma_)',line) and cur=='exec': kind='proof'
        if line.startswith('verus!') or line.startswith('} // verus') or line.startswith('use ') or line.startswith('#'): kind=None
        if kind: c[kind]+=1
        if kind=="exec" and DEBUG: print("EXEC", raw)
        # braces
        for ch in raw:
            if ch=='{':
                if mode and (line == '{' or (re.search(r'\bfn\b', line) and line.endswith('{'))):
                    stack.append(mode); mode=None; clause=False
                elif mode: stack.append('spec')
                elif re.match(r'\s*(proof\s*\{|assert.*by\s*\{|.*\bby\s*\{)',raw) and (not stack or stack[-1]=='exec'): stack.append('proof')
                else: stack.append(stack[-1] if stack else 'exec')
            elif ch=='}':
                if stack: stack.pop()
        if clause and line.endswith('{') : clause=False
    return c
tot={'spec':0,'proof':0,'exec':0}
for p in sys.argv[1:]:
    c=count(p); print('%-28s spec %5d proof %5d exec %5d'%(p.split('/')[-1],c['spec'],c['proof'],c['exec']))
    for k in tot: tot[k]+=c[k]
print('%-28s spec %5d proof %5d exec %5d'%('total',tot['spec'],tot['proof'],tot['exec']))
