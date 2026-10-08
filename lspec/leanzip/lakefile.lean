import Lake
open Lake DSL

/-! Lean spec vs lean-zip's spec. A separate package because lean-zip needs
Lean 4.35.0-rc2: it builds `lspec` (the parent directory) with that toolchain
too. -/
package «lspec-leanzip»

-- lean-zip 2f7a63f plus our fix for kim-em/lean-zip#2586 (branch feat/2586-symbol-counts
-- of our fork, not submitted upstream).
require «lean-zip» from git "https://github.com/zhouxt1/lean-zip" @ "d14fbee0c20d945662effd16c3eed0b4cbfd441e"
require lspec from ".."

lean_lib LeanZipEq

lean_lib LeanZipEnc

lean_exe lsdecode where
  root := `LsDecode
