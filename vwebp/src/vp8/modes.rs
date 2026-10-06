//! Every macroblock's modes, from the first partition, proved to follow
//! `spec::modes`.
use vstd::prelude::*;
use super::spec::*;
use super::tab::*;
use super::bd::Bd;
use super::hdr::*;

verus! {

pub struct MbX {
    pub segment: u8,
    pub skip: bool,
    pub y_mode: u8,
    pub uv_mode: u8,
    pub b_modes: [u8; 16],
}

pub open spec fn nats(s: Seq<u8>) -> Seq<nat> { s.map_values(|m: u8| m as nat) }

impl MbX {
    pub open spec fn view(&self) -> Mb {
        Mb { segment: self.segment as nat, skip: self.skip, y_mode: self.y_mode as nat, uv_mode: self.uv_mode as nat,
             b_modes: nats(self.b_modes@) }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.segment < 4 && self.y_mode <= 4 && self.uv_mode <= 3
        &&& forall|k: int| 0 <= k < 16 ==> #[trigger] self.b_modes@[k] <= 9
    }
}

pub open spec fn row_view(r: Seq<MbX>) -> Seq<Mb> { r.map_values(|m: MbX| m.view()) }
pub open spec fn rows_view(r: Seq<Vec<MbX>>) -> Seq<Seq<Mb>> { r.map_values(|row: Vec<MbX>| row_view(row@)) }

fn read_y_mode_x(bd: &mut Bd) -> (r: u8)
    requires old(bd).wf(),
    ensures final(bd).wf(), final(bd).buf@ == old(bd).buf@, r <= 4,
        (r as nat, final(bd).view()) == read_y_mode(old(bd).buf@, old(bd).view()),
{
    proof { reveal(read_y_mode); }
    if !bd.get(145) { 4 }
    else if !bd.get(156) { if bd.get(163) { 1 } else { 0 } }
    else { if bd.get(128) { 3 } else { 2 } }
}

fn read_uv_mode_x(bd: &mut Bd) -> (r: u8)
    requires old(bd).wf(),
    ensures final(bd).wf(), final(bd).buf@ == old(bd).buf@, r <= 3,
        (r as nat, final(bd).view()) == read_uv_mode(old(bd).buf@, old(bd).view()),
{
    proof { reveal(read_uv_mode); }
    if !bd.get(142) { 0 }
    else if !bd.get(114) { 1 }
    else { if bd.get(183) { 3 } else { 2 } }
}

fn read_b_mode_x(bd: &mut Bd, at: usize) -> (r: u8)
    requires old(bd).wf(), at + 9 <= 900,
    ensures final(bd).wf(), final(bd).buf@ == old(bd).buf@, r <= 9,
        (r as nat, final(bd).view()) == read_b_mode(old(bd).buf@, old(bd).view(), at as int),
{
    proof { reveal(read_b_mode); }
    if !bd.get(KF_B_MODE_PROBS[at]) { return 0; }
    if !bd.get(KF_B_MODE_PROBS[at + 1]) { return 1; }
    if !bd.get(KF_B_MODE_PROBS[at + 2]) { return 2; }
    if !bd.get(KF_B_MODE_PROBS[at + 3]) {
        if !bd.get(KF_B_MODE_PROBS[at + 4]) { 3 } else if bd.get(KF_B_MODE_PROBS[at + 5]) { 6 } else { 5 }
    } else {
        if !bd.get(KF_B_MODE_PROBS[at + 6]) { 4 }
        else if !bd.get(KF_B_MODE_PROBS[at + 7]) { 7 }
        else if bd.get(KF_B_MODE_PROBS[at + 8]) { 9 } else { 8 }
    }
}

/// `edge_modes`.
fn edge_modes_x(mb: &MbX, side: u8) -> (r: [u8; 4])
    requires mb.wf(),
    ensures nats(r@) == edge_modes(mb.view(), side as nat), forall|k: int| 0 <= k < 4 ==> #[trigger] r@[k] <= 9,
{
    let mut r: [u8; 4] = [0; 4];
    let mut k: usize = 0;
    while k < 4
        invariant
            mb.wf(), k <= 4, r@.len() == 4,
            forall|j: int| 0 <= j < k ==> #[trigger] r@[j] as nat == edge_modes(mb.view(), side as nat)[j],
            forall|j: int| 0 <= j < 4 ==> #[trigger] r@[j] <= 9,
        decreases 4 - k,
    {
        let v = if mb.y_mode == 4 {
            if side == 0 { mb.b_modes[12 + k] } else { mb.b_modes[4 * k + 3] }
        } else if mb.y_mode == 0 { 0 } else if mb.y_mode == 1 { 2 } else if mb.y_mode == 2 { 3 } else { 1 };
        r[k] = v;
        k = k + 1;
    }
    proof { assert(nats(r@) =~= edge_modes(mb.view(), side as nat)); }
    r
}

/// `b_modes`.
fn b_modes_x(bd: &mut Bd, above: &[u8; 4], left: &[u8; 4]) -> (r: [u8; 16])
    requires old(bd).wf(), forall|k: int| 0 <= k < 4 ==> #[trigger] above@[k] <= 9, forall|k: int| 0 <= k < 4 ==> #[trigger] left@[k] <= 9,
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, forall|k: int| 0 <= k < 16 ==> #[trigger] r@[k] <= 9,
        (nats(r@), final(bd).view()) == b_modes(old(bd).buf@, old(bd).view(), nats(above@), nats(left@), Seq::empty()),
{
    let ghost buf = bd.buf@;
    let ghost s0 = bd.view();
    let mut r: [u8; 16] = [0; 16];
    let mut b: usize = 0;
    proof { assert(nats(r@).subrange(0, 0) =~= Seq::<nat>::empty()); }
    while b < 16
        invariant
            bd.wf(), bd.buf@ == buf, b <= 16, r@.len() == 16,
            forall|k: int| 0 <= k < 4 ==> #[trigger] above@[k] <= 9, forall|k: int| 0 <= k < 4 ==> #[trigger] left@[k] <= 9,
            forall|k: int| 0 <= k < b ==> #[trigger] r@[k] <= 9,
            b_modes(buf, bd.view(), nats(above@), nats(left@), nats(r@).subrange(0, b as int))
                == b_modes(buf, s0, nats(above@), nats(left@), Seq::empty()),
        decreases 16 - b,
    {
        let a = if b < 4 { above[b] } else { r[b - 4] };
        let l = if b % 4 == 0 { left[b / 4] } else { r[b - 1] };
        let ghost acc = nats(r@).subrange(0, b as int);
        proof {
            let bi = b as int;
            assert((if bi < 4 { nats(above@)[bi] } else { acc[bi - 4] }) == a as nat);
            assert((if bi % 4 == 0 { nats(left@)[bi / 4] } else { acc[bi - 1] }) == l as nat);
            assert((a as usize * 10 + l as usize) * 9 + 9 <= 900) by (nonlinear_arith) requires a <= 9, l <= 9;
        }
        let m = read_b_mode_x(bd, (a as usize * 10 + l as usize) * 9);
        r[b] = m;
        proof {
            assert(nats(r@).subrange(0, b + 1) =~= acc.push(m as nat));
        }
        b = b + 1;
    }
    proof { assert(nats(r@).subrange(0, 16) =~= nats(r@)); }
    r
}

/// `mb_modes`.
fn mb_modes_x(hd: &HdrX, bd: &mut Bd, above: &[u8; 4], left: &[u8; 4]) -> (r: MbX)
    requires old(bd).wf(), hd.wf(), forall|k: int| 0 <= k < 4 ==> #[trigger] above@[k] <= 9, forall|k: int| 0 <= k < 4 ==> #[trigger] left@[k] <= 9,
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, r.wf(),
        (r.view(), final(bd).view()) == mb_modes(hd.view(), old(bd).buf@, old(bd).view(), nats(above@), nats(left@)),
{
    proof { reveal(mb_modes); }
    let segment: u8 = if hd.seg.update_map {
        if !bd.get(hd.seg.tree[0]) {
            if bd.get(hd.seg.tree[1]) { 1 } else { 0 }
        } else {
            if bd.get(hd.seg.tree[2]) { 3 } else { 2 }
        }
    } else {
        0
    };
    let skip = match hd.skip { Some(p) => bd.get(p), None => false };
    let y_mode = read_y_mode_x(bd);
    let b_modes: [u8; 16] = if y_mode == 4 { b_modes_x(bd, above, left) } else { [0; 16] };
    proof {
        if y_mode != 4 {
            assert(nats(b_modes@) =~= Seq::new(16, |k: int| 0nat));
        }
    }
    let uv_mode = read_uv_mode_x(bd);
    MbX { segment, skip, y_mode, uv_mode, b_modes }
}

/// `modes_row`: `above` holds the row above's bottom edges.
fn modes_row_x(hd: &HdrX, bd: &mut Bd, mbw: usize, above: &Vec<[u8; 4]>) -> (r: Vec<MbX>)
    requires
        old(bd).wf(), hd.wf(), above@.len() == mbw,
        forall|x: int, k: int| 0 <= x < mbw && 0 <= k < 4 ==> #[trigger] above@[x]@[k] <= 9,
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, r@.len() == mbw,
        forall|x: int| 0 <= x < mbw ==> #[trigger] r@[x].wf(),
        (row_view(r@), final(bd).view()) == modes_row(hd.view(), old(bd).buf@, old(bd).view(), mbw as nat,
            above@.map_values(|a: [u8; 4]| nats(a@)), dc4(), Seq::empty()),
{
    let ghost buf = bd.buf@;
    let ghost s0 = bd.view();
    let ghost av = above@.map_values(|a: [u8; 4]| nats(a@));
    let mut r: Vec<MbX> = Vec::new();
    let mut left: [u8; 4] = [0; 4];
    let mut x: usize = 0;
    proof {
        assert(nats(left@) =~= dc4());
        assert(row_view(r@) =~= Seq::<Mb>::empty());
    }
    while x < mbw
        invariant
            bd.wf(), bd.buf@ == buf, hd.wf(), x <= mbw, r@.len() == x, above@.len() == mbw,
            av == above@.map_values(|a: [u8; 4]| nats(a@)),
            forall|x: int, k: int| 0 <= x < mbw && 0 <= k < 4 ==> #[trigger] above@[x]@[k] <= 9,
            forall|k: int| 0 <= k < 4 ==> #[trigger] left@[k] <= 9,
            forall|j: int| 0 <= j < x ==> #[trigger] r@[j].wf(),
            modes_row(hd.view(), buf, bd.view(), mbw as nat, av, nats(left@), row_view(r@))
                == modes_row(hd.view(), buf, s0, mbw as nat, av, dc4(), Seq::empty()),
        decreases mbw - x,
    {
        let ghost r0 = r@;
        let ghost sb = bd.view();
        proof {
            assert(av.len() == mbw);
            assert(av[x as int] == nats(above@[x as int]@));
        }
        let mb = mb_modes_x(hd, bd, &above[x], &left);
        left = edge_modes_x(&mb, 1);
        r.push(mb);
        proof { assert(row_view(r@) =~= row_view(r0).push(mb.view())); }
        x = x + 1;
    }
    r
}

/// Every macroblock's modes (`modes`).
pub fn modes_x(hd: &HdrX, bd: &mut Bd, mbw: usize, mbh: usize) -> (r: Vec<Vec<MbX>>)
    requires old(bd).wf(), hd.wf(), mbw >= 1,
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, r@.len() == mbh,
        forall|y: int| 0 <= y < mbh ==> (#[trigger] r@[y])@.len() == mbw,
        forall|y: int, x: int| 0 <= y < mbh && 0 <= x < mbw ==> (#[trigger] r@[y]@[x]).wf(),
        (rows_view(r@), final(bd).view()) == modes(hd.view(), old(bd).buf@, old(bd).view(), mbw as nat, mbh as nat, Seq::empty()),
{
    let ghost buf = bd.buf@;
    let ghost s0 = bd.view();
    let mut r: Vec<Vec<MbX>> = Vec::new();
    let mut above: Vec<[u8; 4]> = Vec::new();
    let mut x: usize = 0;
    while x < mbw
        invariant x <= mbw, above@.len() == x, forall|j: int| 0 <= j < x ==> #[trigger] above@[j]@ == seq![0u8, 0, 0, 0],
        decreases mbw - x,
    {
        let z: [u8; 4] = [0; 4];
        proof { assert(z@ =~= seq![0u8, 0, 0, 0]); }
        above.push(z);
        x = x + 1;
    }
    proof {
        assert(above@.map_values(|a: [u8; 4]| nats(a@)) =~= Seq::new(mbw as nat, |x: int| dc4())) by {
            assert forall|j: int| 0 <= j < mbw implies #[trigger] nats(above@[j]@) == dc4() by {
                assert(nats(above@[j]@) =~= dc4());
            }
        }
        assert(rows_view(r@) =~= Seq::<Seq<Mb>>::empty());
    }
    let mut y: usize = 0;
    while y < mbh
        invariant
            bd.wf(), bd.buf@ == buf, hd.wf(), y <= mbh, r@.len() == y, above@.len() == mbw, mbw >= 1,
            forall|x: int, k: int| 0 <= x < mbw && 0 <= k < 4 ==> #[trigger] above@[x]@[k] <= 9,
            forall|j: int| 0 <= j < y ==> (#[trigger] r@[j])@.len() == mbw,
            forall|j: int, x: int| 0 <= j < y && 0 <= x < mbw ==> (#[trigger] r@[j]@[x]).wf(),
            above@.map_values(|a: [u8; 4]| nats(a@)) == (if y == 0 { Seq::new(mbw as nat, |x: int| dc4()) }
                else { Seq::new(mbw as nat, |x: int| edge_modes(rows_view(r@).last()[x], 0)) }),
            modes(hd.view(), buf, bd.view(), mbw as nat, mbh as nat, rows_view(r@))
                == modes(hd.view(), buf, s0, mbw as nat, mbh as nat, Seq::empty()),
        decreases mbh - y,
    {
        let ghost r0 = r@;
        let row = modes_row_x(hd, bd, mbw, &above);
        let mut next: Vec<[u8; 4]> = Vec::new();
        let mut x: usize = 0;
        while x < mbw
            invariant
                x <= mbw, row@.len() == mbw, next@.len() == x,
                forall|j: int| 0 <= j < mbw ==> #[trigger] row@[j].wf(),
                forall|j: int, k: int| 0 <= j < x && 0 <= k < 4 ==> #[trigger] next@[j]@[k] <= 9,
                forall|j: int| 0 <= j < x ==> #[trigger] nats(next@[j]@) == edge_modes(row@[j].view(), 0),
            decreases mbw - x,
        {
            let e = edge_modes_x(&row[x], 0);
            next.push(e);
            x = x + 1;
        }
        let ghost rv = row_view(row@);
        r.push(row);
        above = next;
        proof {
            assert(rows_view(r@) =~= rows_view(r0).push(rv));
            assert(above@.map_values(|a: [u8; 4]| nats(a@)) =~= Seq::new(mbw as nat, |x: int| edge_modes(rows_view(r@).last()[x], 0)));
        }
        y = y + 1;
    }
    r
}

} // verus!
