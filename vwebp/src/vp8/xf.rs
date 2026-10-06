//! The inverse transforms (RFC 6386 20.8, idct_add.c), proved to compute
//! `spec::idct` and `spec::iwht`.
use vstd::prelude::*;
use super::spec::*;
use super::hdr::*;
use super::tok::*;

verus! {

fn ms_x(x: i32) -> (r: i32)
    requires -32768 <= x <= 32767,
    ensures r as int == ms(x as int), -17734 <= r <= 17734,
{
    proof { assert(-1162215424 <= x * 35468 <= 1162179956) by (nonlinear_arith) requires -32768 <= x <= 32767; }
    let y = x * 35468;
    let r = y >> 16u32;
    proof {
        assert(r as int == (y as int) / 65536) by (bit_vector) requires r == y >> 16u32;
        assert(-17734int <= (y as int) / 65536 <= 17733int) by (nonlinear_arith)
            requires -1162215424 <= y <= 1162179956;
    }
    r
}

fn mc_x(x: i32) -> (r: i32)
    requires -32768 <= x <= 32767,
    ensures r as int == mc(x as int), -42814 <= r <= 42813,
{
    proof { assert(-658341888 <= x * 20091 <= 658321797) by (nonlinear_arith) requires -32768 <= x <= 32767; }
    let y = x * 20091;
    let r = y >> 16u32;
    proof {
        assert(r as int == (y as int) / 65536) by (bit_vector) requires r == y >> 16u32;
        assert(-10046int <= (y as int) / 65536 <= 10045int) by (nonlinear_arith)
            requires -658341888 <= y <= 658321797;
    }
    x + r
}

/// `idct_col`: column `k`'s first pass.
fn idct_col_x(i: &[i32; 16], k: usize) -> (r: [i32; 4])
    requires k < 4, c16(i@),
    ensures ints(r@) == idct_col(ints(i@), k as int), c16(r@),
{
    let a1 = i[k] + i[8 + k];
    let b1 = i[k] - i[8 + k];
    let c1 = ms_x(i[4 + k]) - mc_x(i[12 + k]);
    let d1 = mc_x(i[4 + k]) + ms_x(i[12 + k]);
    let r = [wrap16_x(a1 + d1), wrap16_x(b1 + c1), wrap16_x(b1 - c1), wrap16_x(a1 - d1)];
    proof { assert(ints(r@) =~= idct_col(ints(i@), k as int)); }
    r
}

/// `idct`: the residual of a block, each value within 16 bits / 8.
pub fn idct_x(i: &[i32; 16]) -> (r: [i32; 16])
    requires c16(i@),
    ensures ints(r@) == idct(ints(i@)), forall|j: int| 0 <= j < 16 ==> -16384 <= #[trigger] r@[j] <= 16384,
{
    proof { reveal(idct); }
    let ghost iv = ints(i@);
    let mut t: [i32; 16] = [0; 16];
    let mut k: usize = 0;
    while k < 4
        invariant
            k <= 4, c16(i@), iv == ints(i@), c16(t@),
            forall|kk: int, rr: int| 0 <= kk < k && 0 <= rr < 4 ==> t@[4 * rr + kk] as int == #[trigger] idct_col(iv, kk)[rr],
        decreases 4 - k,
    {
        let c = idct_col_x(i, k);
        t[k] = c[0];
        t[4 + k] = c[1];
        t[8 + k] = c[2];
        t[12 + k] = c[3];
        proof {
            assert forall|kk: int, rr: int| 0 <= kk < k + 1 && 0 <= rr < 4 implies t@[4 * rr + kk] as int == #[trigger] idct_col(iv, kk)[rr] by {
                if kk == k as int {
                    assert(ints(c@)[rr] == c@[rr] as int);
                }
            }
        }
        k = k + 1;
    }
    let ghost tv = ints(t@);
    proof {
        assert(tv =~= idct1(iv)) by {
            assert forall|j: int| 0 <= j < 16 implies #[trigger] tv[j] == idct1(iv)[j] by {
                assert(j == 4 * (j / 4) + j % 4);
            }
        }
    }
    let mut r: [i32; 16] = [0; 16];
    let mut row: usize = 0;
    while row < 4
        invariant
            row <= 4, c16(t@), tv == ints(t@), tv == idct1(iv),
            forall|j: int| 0 <= j < 4 * row ==> r@[j] as int == #[trigger] idct(iv)[j],
            forall|j: int| 0 <= j < 16 ==> -16384 <= #[trigger] r@[j] <= 16384,
        decreases 4 - row,
    {
        proof { reveal(idct); }
        let t0 = t[4 * row];
        let t1 = t[4 * row + 1];
        let t2 = t[4 * row + 2];
        let t3 = t[4 * row + 3];
        let a1 = t0 + t2;
        let b1 = t0 - t2;
        let c1 = ms_x(t1) - mc_x(t3);
        let d1 = mc_x(t1) + ms_x(t3);
        let v0 = a1 + d1 + 4;
        let v1 = b1 + c1 + 4;
        let v2 = b1 - c1 + 4;
        let v3 = a1 - d1 + 4;
        let o0 = v0 >> 3u32;
        let o1 = v1 >> 3u32;
        let o2 = v2 >> 3u32;
        let o3 = v3 >> 3u32;
        proof {
            assert(o0 as int == (v0 as int) / 8) by (bit_vector) requires o0 == v0 >> 3u32;
            assert(o1 as int == (v1 as int) / 8) by (bit_vector) requires o1 == v1 >> 3u32;
            assert(o2 as int == (v2 as int) / 8) by (bit_vector) requires o2 == v2 >> 3u32;
            assert(o3 as int == (v3 as int) / 8) by (bit_vector) requires o3 == v3 >> 3u32;
        }
        r[4 * row] = o0;
        r[4 * row + 1] = o1;
        r[4 * row + 2] = o2;
        r[4 * row + 3] = o3;
        proof {
            assert forall|j: int| 0 <= j < 4 * (row + 1) implies r@[j] as int == #[trigger] idct(iv)[j] by {
                if j >= 4 * row {
                    assert(j / 4 == row as int);
                }
            }
        }
        row = row + 1;
    }
    proof { reveal(idct); assert(ints(r@) =~= idct(iv)); }
    r
}

/// `iwht`: the Y2 block's inverse WHT, each Y block's DC.
pub fn iwht_x(i: &[i32; 16]) -> (r: [i32; 16])
    requires c16(i@),
    ensures ints(r@) == iwht(ints(i@)), c16(r@),
{
    proof { reveal(iwht); }
    let ghost iv = ints(i@);
    let mut o: [i32; 16] = [0; 16];
    let mut k: usize = 0;
    while k < 4
        invariant
            k <= 4, c16(i@), iv == ints(i@), c16(o@),
            forall|kk: int, rr: int| 0 <= kk < k && 0 <= rr < 4 ==> o@[4 * rr + kk] as int == #[trigger] iwht_col(iv, kk)[rr],
        decreases 4 - k,
    {
        let a1 = i[k] + i[12 + k];
        let b1 = i[4 + k] + i[8 + k];
        let c1 = i[4 + k] - i[8 + k];
        let d1 = i[k] - i[12 + k];
        o[k] = wrap16_x(a1 + b1);
        o[4 + k] = wrap16_x(c1 + d1);
        o[8 + k] = wrap16_x(a1 - b1);
        o[12 + k] = wrap16_x(d1 - c1);
        k = k + 1;
    }
    let ghost ov = ints(o@);
    proof {
        assert(ov =~= iwht1(iv)) by {
            assert forall|j: int| 0 <= j < 16 implies #[trigger] ov[j] == iwht1(iv)[j] by {
                assert(j == 4 * (j / 4) + j % 4);
            }
        }
    }
    let mut r: [i32; 16] = [0; 16];
    let mut row: usize = 0;
    while row < 4
        invariant
            row <= 4, c16(o@), ov == ints(o@), ov == iwht1(iv), c16(r@),
            forall|j: int| 0 <= j < 4 * row ==> r@[j] as int == #[trigger] iwht(iv)[j],
        decreases 4 - row,
    {
        proof { reveal(iwht); }
        let a1 = o[4 * row] + o[4 * row + 3];
        let b1 = o[4 * row + 1] + o[4 * row + 2];
        let c1 = o[4 * row + 1] - o[4 * row + 2];
        let d1 = o[4 * row] - o[4 * row + 3];
        let v0 = a1 + b1 + 3;
        let v1 = c1 + d1 + 3;
        let v2 = a1 - b1 + 3;
        let v3 = d1 - c1 + 3;
        let o0 = v0 >> 3u32;
        let o1 = v1 >> 3u32;
        let o2 = v2 >> 3u32;
        let o3 = v3 >> 3u32;
        proof {
            assert(o0 as int == (v0 as int) / 8) by (bit_vector) requires o0 == v0 >> 3u32;
            assert(o1 as int == (v1 as int) / 8) by (bit_vector) requires o1 == v1 >> 3u32;
            assert(o2 as int == (v2 as int) / 8) by (bit_vector) requires o2 == v2 >> 3u32;
            assert(o3 as int == (v3 as int) / 8) by (bit_vector) requires o3 == v3 >> 3u32;
        }
        r[4 * row] = wrap16_x(o0);
        r[4 * row + 1] = wrap16_x(o1);
        r[4 * row + 2] = wrap16_x(o2);
        r[4 * row + 3] = wrap16_x(o3);
        proof {
            assert forall|j: int| 0 <= j < 4 * (row + 1) implies r@[j] as int == #[trigger] iwht(iv)[j] by {
                if j >= 4 * row {
                    assert(j / 4 == row as int);
                }
            }
        }
        row = row + 1;
    }
    proof { reveal(iwht); assert(ints(r@) =~= iwht(iv)); }
    r
}

} // verus!
