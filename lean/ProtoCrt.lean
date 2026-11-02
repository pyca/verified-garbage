import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Bignum.RISCV64.Crt

/-! Throwaway, unproven: the CRT with a one-pass masked table scan and `R² mod p` kept for the
recombination. Bench branch only; never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp output)
open VG.Impl.Bignum.RISCV64.Crt
open VG.Impl.Bignum.RISCV64.ModExp (sqrOp table)

namespace ProtoCrt

/-- The 16 masks `-(j = d)` (`d` in `a1`) at `t6 = a7 - 256` (the prime's header). -/
def masks : List Instr :=
  [.addi .t6 .a7 (-256), .li .t3 0] ++ (List.range 16).flatMap fun j =>
    [.logicImm .xor .t2 .a1 j, .addi .t2 .t2 (-1), .shift .srl .d .t2 .t2 63, .sub .t2 .t3 .t2,
      .store .d .t2 .t6 (8 * j)]

/-- One word of the scan: `[a2] := OR_j (T_j[i] & m_j)`, `T_0[i]` at `t4`. -/
def scanWord : List Instr :=
  [.li .s0 0, .addi .t3 .t4 0] ++ (List.range 16).flatMap (fun j =>
    [.load .d .s2 .t3 0, .load .d .s3 .t6 (8 * j), .logic .and .s2 .s2 .s3, .logic .or .s0 .s0 .s2] ++
      (if j < 15 then [.add .t3 .t3 .s5] else [])) ++
  [.store .d .s0 .a2 0, .addi .a2 .a2 8, .addi .t4 .t4 8]

/-- `T_d` into array 5, `d` in `a1`. -/
def select2 : Prog isa :=
  .seq (.block (masks ++ [.li .s8 0] ++ ModExp.entry .t4 .s8 ++ base .a2 5 ++ [.addi .t5 .t0 0]))
    (countLoop .t5 scanWord)

def window2 : Prog isa :=
  .seq (sqrOp 6 6 5) (.seq (sqrOp 6 6 5) (.seq (sqrOp 6 6 5) (.seq (sqrOp 6 6 5)
    (.seq (.block [.shift .srl .d .a1 .s7 60]) (.seq select2 (.seq (montOp 6 6 5)
      (.block [.shift .sll .d .s7 .s7 4])))))))

def byteWin2 : Prog isa :=
  .seq (.block [.load .b .s7 .s9 0, .shift .sll .d .s7 .s7 56, .addi .s9 .s9 1]) (.seq window2 window2)

def powWin2 : Prog isa :=
  .seq table (.seq (.loop (.seq byteWin2 (.block [.addi .s10 .s10 (-1)])) (.nonzero .s10)) (montOp 4 6 7))

/-- `power`, with the new scan, and for `keep` `R² mod p` copied to `X`'s array 3. -/
def power2 (xj oD oLen : Nat) (keep : Bool) : Prog isa :=
  .seq (.block ([.addi .t3 .a7 0] ++ xb .t4 xj)) (.seq copyN
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3))
  (.seq (r2Prime 4)
  (.seq (if keep then .seq (.block (xb .t3 3 ++ base .t4 1)) copyN else .block [])
  (.seq reduceIn
  (.seq (.block [.load .d .s9 .s6 oD, .load .d .s10 .s6 oLen]) powWin2))))))

/-- `recombineP`, `R² mod p` copied back from `X`'s array 3 instead of recomputed. -/
def recombineP2 : Prog isa :=
  .seq (.block [.load .d .s10 .s6 oQLen])
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3))
  (.seq (.seq (.block (base .t3 1 ++ xb .t4 3)) copyN)
  (.seq (.block (base .t3 7 ++ base .t4 1)) (.seq copyN
  (.seq (.block (xb .s9 1)) (.seq ModArith.reduce64
  (.seq (.block (base .t3 4 ++ [.add .t3 .t3 .s5, .addi .t3 .t3 (-16), .li .s0 0, .store .d .s0 .t3 0] ++
      base .a5 4 ++ base .a6 3 ++ base .a7 1))
  (.seq subMod64 (.seq (.block ([.addi .a7 .ra 0] ++ base .t3 3 ++ base .t4 0)) (.seq ModArith.addMask64
  (.seq (.block (base .t3 6 ++ xb .t4 7)) (.seq copyN
  (.seq (montOp 5 3 6) (montOp 4 5 7))))))))))))))

/-- The CRT with either change (`scan`: the new scan; `keep`: `R² mod p` kept). -/
def crt2 (scan keep : Bool) : Prog isa :=
  let pw := fun xj oD oLen k => if scan then power2 xj oD oLen k else
    (if k then power2 xj oD oLen true else power xj oD oLen)
  -- with `scan` false and `keep` true, `power2` still uses the new scan; keep the old one then.
  let pwOld := fun xj oD oLen (k : Bool) =>
    if k then
      .seq (.block ([.addi .t3 .a7 0] ++ xb .t4 xj)) (.seq copyN
      (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3))
      (.seq (r2Prime 4) (.seq (.seq (.block (xb .t3 3 ++ base .t4 1)) copyN) (.seq reduceIn
      (.seq (.block [.load .d .s9 .s6 oD, .load .d .s10 .s6 oLen]) ModExp.powWin))))))
    else power xj oD oLen
  let pw' := if scan then pw else pwOld
  .seq (.block (save ++ args ++ setupX)) (.seq loadX (.seq checks (.seq loadIn
  (.seq (.block (setupP oBP oPLen)) (.seq (pw' 4 oDP oPLen keep)
  (.seq (.block (setupP oBQ oQLen)) (.seq (pw' 5 oDQ oQLen false) (.seq exportM2
  (.seq (.block (setupP oBP oPLen)) (.seq (if keep then recombineP2 else recombineP) (.seq recombineX
  (.seq (.block [.addi .a7 .s6 hdrBytes, .addi .s5 .s11 0, .load .d .s10 .s6 oOut, .load .d .s11 .s6 oNLen,
      .load .d .s9 .s6 oMask])
    (.seq output (.block restore))))))))))))))

def emitFn (name sig : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "rsa_proto7") "super" ++ "}\n"

def p8 (ns : List String) : String := ", ".intercalate (ns.map fun n => s!"{n}: *const u8, {n}_len: usize")

end ProtoCrt

open ProtoCrt in
def main (args : List String) : IO Unit := do
  let crtSig := s!"(out: *mut u8, out_len: usize, {p8 ["n", "input", "p", "q", "dp", "dq", "qinv"]}, scratch: *mut u64, scratch_len: usize) -> u32"
  IO.FS.writeFile (args.headD "rsa_proto7.rs") ("//! Unproven prototype, for local checks only.\n#![allow(clippy::missing_safety_doc, clippy::too_many_arguments)]\n" ++
    emitFn "vg_proto_crt_scan" crtSig (crt2 true false) ++
    emitFn "vg_proto_crt_keep" crtSig (crt2 false true) ++
    emitFn "vg_proto_crt_both" crtSig (crt2 true true) ++
    emitFn "vg_proto_crt_base" crtSig (crt2 false false))
