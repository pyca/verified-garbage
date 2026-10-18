module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Impl.Gcm.AArch64.Stitch

/-!
# AES-GCM on AArch64: the path for TLS records, interleaved

The path for TLS records (`Fast.lean`) of the functions with the powers
(`_with_powers`, `_store_powers`), for CPUs with FEAT_AES, FEAT_PMULL and
FEAT_SHA3: the first `128 ⌊len / 128⌋` bytes of the
text encrypted (or decrypted) and hashed by the interleaved loops of
`Impl.Gcm.AArch64.Stitch`, then the rest as `Fast.lean` does.

* The loops read the table of keys at `W + 512` (`Stitch.tbl`), which
  `tbl` writes from `H'` to `H'⁸` in `tReg`/`sReg`
  (`Impl.Gcm.AArch64.Pmull`): computed as `vg_ghash_aes` computes them
  (`powTbl`, for `_store_powers`), or loaded from `pw` (`pwTbl`, for
  `_with_powers`). Plain `seal` and `open`, which would compute the powers
  on every call, keep `Fast.lean`'s path.
* Only a text of at least `minLen` bytes takes the loops (`thr`); a shorter
  one takes `Fast.lean`'s path, as the `_aes` functions do. Writing the
  table and the loops' first and last steps cost about as much as 3.4 to 6.2
  of the loops' 128-byte steps save (measured on Neoverse N2: 600-byte texts
  slower, 1023-byte ones faster; pyca/verified-garbage#2758).
* `open` decrypts the first bytes before it knows whether the tag is right:
  it keeps the first counter block at `W + cbO`, and if the tag is wrong
  encrypts those bytes again from it, which leaves them as they were.
-/

@[expose] public section

namespace VG.Impl.AesGcm.AArch64.Stitch

open VG.AArch64
open VG.Impl.AesGcm.AArch64.Fast
open VG.Impl.Gcm.AArch64.Pmull (tReg sReg powers loadPw loadRev Y)

/-- Where `open` keeps the first counter block. -/
def cbO : Nat := 320

/-- The table of keys from `H'` to `H'⁸` in `tReg` and `sReg`: each power
with its halves swapped, then the sums of each power's halves, two to a
register, for the pairs of `ghPart`. -/
def tbl : List Instr :=
  (List.range 8).flatMap (fun k => [.strq (sReg (k + 1)) .x19 (Gcm.AArch64.Stitch.sOff (k + 1))]) ++
  (List.range 4).flatMap fun p =>
    [.vop (.logic .eor .v2 (sReg (Gcm.AArch64.Stitch.pk p)) (tReg (Gcm.AArch64.Stitch.pk p))),
     .vop (.logic .eor .v3 (sReg (Gcm.AArch64.Stitch.pl p)) (tReg (Gcm.AArch64.Stitch.pl p))),
     .vop (.ext .v4 .v2 .v3 8), .strq .v4 .x19 (Gcm.AArch64.Stitch.kOff p)]

/-- The table, from the powers computed from `H'` (kept at `W + hO`). -/
def powTbl : List Instr := hReload ++ powers ++ tbl

/-- The table, from the powers in `pw`, the stack argument at `sp + k`. -/
def pwTbl (k : Nat) : List Instr :=
  ([.ldrSp .x5 k] : List Instr) ++ (List.range 8).flatMap (fun k => loadPw (k + 1)) ++ tbl

/-- The shortest text the loops take, in bytes: six of their steps. -/
def minLen : Nat := 768

/-- `x9 = ⌊(x7 + 256) / 1024⌋`, zero exactly when the text's length `x7` is
less than `minLen`. -/
def thr : List Instr := [.addImm .x .x9 .x7 (1024 - minLen), .lsr .x .x9 .x9 10]

/-- `x9 = 128 ⌊x26 / 128⌋`, the bytes the loops take. -/
def whole : List Instr := [.lsr .x .x9 .x26 7, .lsl .x .x9 .x9 7]

/-- The loop `l` on the first `128 ⌊x26 / 128⌋` bytes at `x23`, after `pre`
and the table `tb`, if there are any. -/
def stitched (pre tb : List Instr) (l : Prog isa) : Prog isa :=
  .seq (.block [.lsr .x .x9 .x26 7]) (.ite (.zero .x .x9) (.block []) (.seq (.block (pre ++ tb)) l))

variable (c : Callees)

/-- `runWithP`, the first bytes encrypted and hashed by the interleaved loop. -/
def runWithS (tb : List Instr) (cl : Prog isa) : Prog isa :=
  .seq front
  (.seq (stitched [] tb Gcm.AArch64.Stitch.enc)
  (.seq (.block (whole ++ [.add .x .x23 .x23 .x9, mov .x27 .x23, .sub .x .x24 .x26 .x9, imm .x25 0]))
  (.seq (cryptAl c)
  (.seq (.block ([mov .x23 .x27] ++ whole ++ [.sub .x .x24 .x26 .x9] ++ absSeg2 16))
  (.seq cl
  (.seq (.block (hReload ++ loadRev Y .x20 16 ++ [mov .x13 .x24, mov .x12 .x23]))
  (.seq padMul
  (.seq (.block lensTag)
  (.seq (ctrCall c)
  (.seq (.block tagOut)
    (.block restore)))))))))))

/-- `openRunWithP`, the first bytes decrypted and hashed by the interleaved
loop, the first counter block kept; the rest decrypted if the tag is right,
and the first bytes encrypted again from it if not. -/
def openRunWithS (tb : List Instr) (cl : Prog isa) : Prog isa :=
  .seq front
  (.seq (.block [.ldrq .v0 .x20 48, .strq .v0 .x19 cbO])
  (.seq (stitched [] tb Gcm.AArch64.Stitch.dec)
  (.seq (.block (whole ++ [.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] ++ absSeg2 16))
  (.seq cl
  (.seq (.block (hReload ++ loadRev Y .x20 16 ++ [mov .x13 .x24, mov .x12 .x23]))
  (.seq padMul
  (.seq (.block (lensTagAt uO))
  (.seq (ctrCall c)
  (.seq cmp
  (.seq (.block [imm .x27 1, .sub .x .x27 .x27 .x10])
  (.seq (.ite (.zero .x .x27)
      (.seq (.block ([.ldrq .v0 .x19 cbO, .strq .v0 .x20 48, .ldr .x .x23 .x19 dataO,
          .ldr .x .x26 .x19 lenO] ++ whole ++ [mov .x24 .x9, imm .x25 0])) (cryptAl c))
      (.seq (.block ([.ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] ++ whole ++
          [.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0])) (cryptAl c)))
    (.block [mov .x0 .x27]))))))))))))

/-- `openFastP` with `openRunWithS`. -/
def openFastS (tb : List Instr) (cl : Prog isa) : Prog isa :=
  .seq tagLenOk
  (.seq (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn (openRunWithS c tb cl)))
    (.block restore))

/-- `vg_aes_gcm_seal`, with `work` at `sp + k`: below `minLen` bytes,
`Fast.lean`'s path. -/
def sealWithS (k : Nat) (tb : List Instr) (cl : Prog isa) : Prog isa :=
  .seq (.block (oneEntry k ++ stashArg 0))
    (.seq cond (.ite (.zero .x .x10)
      (.seq (.block thr) (.ite (.zero .x .x9) (runWithP c cl) (runWithS c tb cl)))
      (sealRest c)))

/-- `vg_aes_gcm_open`, with `work` at `sp + k`: below `minLen` bytes,
`Fast.lean`'s path. -/
def openWithS (k : Nat) (tb : List Instr) (cl : Prog isa) : Prog isa :=
  .seq (.block (oneEntry k ++ stashArg 8 ++ ([.ldrSp .x12 0] : List Instr)))
    (.seq cond (.ite (.zero .x .x10)
      (.seq (.block thr) (.ite (.zero .x .x9) (openFastP c cl) (openFastS c tb cl)))
      (openRest c)))

/-- `vg_aes_gcm_seal_with_powers`, hashing the rest by `gh`. -/
def sealWithPw (gh : Fn) : Prog isa := sealWithS c 16 (pwTbl 8) (pwCall 8 gh)

/-- `vg_aes_gcm_open_with_powers`, hashing the rest by `gh`. -/
def openWithPw (gh : Fn) : Prog isa := openWithS c 24 (pwTbl 16) (pwCall 16 gh)

/-- `vg_aes_gcm_seal_store_powers`, `gh` storing the powers. -/
def sealStorePw (gh : Fn) : Prog isa := sealWithS c 16 powTbl (pwCall 8 gh)

/-- `vg_aes_gcm_open_store_powers`, `gh` storing the powers. -/
def openStorePw (gh : Fn) : Prog isa := openWithS c 24 powTbl (pwCall 16 gh)

end VG.Impl.AesGcm.AArch64.Stitch
