# Timing lean-zip

`LzTime.lean` is a driver for lean-zip (github.com/kim-em/lean-zip, 2f7a63f):
copy it into a lean-zip checkout, add

```
lean_exe lztime where
  root := `LzTime
```

to its `lakefile.lean`, and `lake build lztime` (with elan; the toolchain
is lean-zip's own). Then

    lztime inflate FILE.raw OUTPUT_SIZE 10    # decode a raw DEFLATE stream
    lztime deflate FILE LEVEL 3               # compress

print MB/s of the fastest run (the output size, for `deflate`). The numbers
in `vdeflate/README.md` come from this on the same machine as the others.
