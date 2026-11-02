module

public import VerifiedGarbage.Impl.Sha3.RISCV64.Pieces
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Arith
public import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA on RISC-V: `vg_mldsa{44,65,87}_sign_message` and `_verify_message`

`sign_message(sk = a0, msg = a1, msg_len = a2, ctx = a3, ctx_len = a4,
rnd = a5, sig = a6, scratch = a7) -> a0` and `verify_message(pk = a0,
msg = a1, msg_len = a2, ctx = a3, ctx_len = a4, sig = a5, scratch = a6) -> a0`:
`ML-DSA.Sign` and `ML-DSA.Verify` (FIPS 204 Algorithms 2 and 3), as calls of
the sponge functions (`hash`, `Impl/Sha3/RISCV64/Pieces.lean`) and of the
functions on `μ` (`vg_mldsa*_sign`, `vg_mldsa*_verify`), named `n` and with
the code `f`.

If `ctx_len ≥ 256` (`ctx_len >> 8 ≠ 0`) they return 2 at once. Otherwise
they work in the 1 KiB after the working space of the function on `μ` (at
`oE p`, from `scratch`; its address `E` is kept in `s8`): the Keccak state
(200 bytes, in the 840 bytes `hash` is given, as on PPC64LE, whose sponge
functions also have a working space there); `μ` (64 bytes); our caller's
registers that we use and the return address (`saveRegs`, at `oSV`); and the
two bytes `0 ‖ ctx_len` of the formatted message (at `oHdr`). They use no
stack of their own; the functions they call use 1168 bytes below the stack
pointer. The arguments stay in `s0`–`s7`, which the functions called keep.

* Signing computes `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, with `tr` the 64
  bytes of `sk` at 64, and calls `vg_mldsa*_sign(sk, μ, rnd, sig, scratch)`.
* Verification first computes `tr = H(pk, 64)` into the buffer of `μ`, then
  `μ` from it likewise, and calls `vg_mldsa*_verify(pk, μ, sig, scratch)`.

Every address and branch depends only on the pointers and the lengths, and
the calls' own leakage.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Message

open VG.RISCV64
open VG.Spec.MlDsa (Params)
open VG.Impl.Sha3.RISCV64.Pieces (Piece hash)
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Impl.Ed25519.RISCV64.Whole (saveRegs restoreRegs)

/-- Where the 1 KiB starts in `scratch`: after the working space of the
functions on `μ`. -/
def oE (p : Params) : Nat := 8 * Spec.MlDsa.scratchWords p

/-! ## The 1 KiB, from `E` -/

/-- The bytes `hash` is given (the Keccak state is their first 200). -/
def nK : Nat := 840
/-- `μ`. -/
def oMU : Nat := 840
/-- Our caller's registers and the link register. -/
def oSV : Nat := 904
/-- The two bytes of the formatted message. -/
def oHdr : Nat := 984

/-! ## Entry and exit -/

/-- `0 ‖ ctx_len` (`ctx_len` in `s4`) at `oHdr`. -/
def hdr : List Instr := [.li .t0 0, .store .b .t0 .s8 oHdr, .store .b .s4 .s8 (oHdr + 1)]

/-- `E` (`scratch` in `sr` plus `oE p`) in `t2`. -/
def base (sr : Reg) (p : Params) : List Instr :=
  Impl.MlDsa.RISCV64.Arith.loadImm .t2 (oE p) ++ ([.add .t2 sr .t2] : List Instr)

/-- `E` in `t2`, our caller's registers `rs` and the return address saved
there, and the moves `ms` (to, from) of the arguments. -/
def enter (sr : Reg) (p : Params) (rs : List Reg) (ms : List (Reg × Reg)) : List Instr :=
  base sr p ++ (saveRegs .t2 oSV rs ++ ms.map (fun m => mov m.1 m.2) ++ hdr)

/-- The formatted message after its first piece: `0 ‖ ctx_len`, the
context (`s3`, `s4`), the message (`s1`, `s2`). -/
def fmtPieces : List Piece := [⟨.s8, oHdr, .imm 2⟩, ⟨.s3, 0, .reg .s4⟩, ⟨.s1, 0, .reg .s2⟩]

/-- `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, for the 64 bytes `tr` at `tr`. -/
def muHash (tr : Piece) : Prog isa := hash .s8 (tr :: fmtPieces) .s8 oMU 64

/-- `tr = H(pk, 64)` (`pk` in `s0`) to the buffer of `μ`, absorbing `pk` in
two pieces (its first 1024 bytes, then the rest), since a piece's length is
an immediate of 12 bits (`Len.set`). -/
def trHash (p : Params) : Prog isa :=
  hash .s8 [⟨.s0, 0, .imm 1024⟩, ⟨.s0, 1024, .imm (p.pkLen - 1024)⟩] .s8 oMU 64

/-- If `ctx_len < 256`, `body`; otherwise return 2. -/
def top (body : Prog isa) : Prog isa :=
  .seq (.block [.shift .srl .d .t1 .a4 8]) (.ite (.zero .t1) body (.block [.li .a0 2]))

/-! ## The functions -/

/-- The registers signing uses: `sk`, `msg`, `msg_len`, `ctx`, `ctx_len`,
`rnd`, `sig`, `scratch` and `E` (the base of the saves, last). -/
def signRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8]

def signMs : List (Reg × Reg) :=
  [(.s0, .a0), (.s1, .a1), (.s2, .a2), (.s3, .a3), (.s4, .a4), (.s5, .a5), (.s6, .a6), (.s7, .a7),
    (.s8, .t2)]

/-- `vg_mldsa*_sign_message` for the parameter set `p`, calling the signing
function on `μ` `f`, named `n`. -/
def signMessage (n : String) (f : Prog isa) (p : Params) : Prog isa :=
  top <| .seq (.block (enter .a7 p signRegs signMs)) <| .seq (muHash ⟨.s0, 64, .imm 64⟩) <|
  .seq (.seq (.block [mov .a0 .s0, .addi .a1 .s8 oMU, mov .a2 .s5, mov .a3 .s6, mov .a4 .s7]) (.call n f))
    (.block (restoreRegs .s8 oSV signRegs))

/-- The registers verification uses: `pk`, `msg`, `msg_len`, `ctx`,
`ctx_len`, `sig`, `scratch` and `E`. -/
def verifyRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s7, .s8]

def verifyMs : List (Reg × Reg) :=
  [(.s0, .a0), (.s1, .a1), (.s2, .a2), (.s3, .a3), (.s4, .a4), (.s5, .a5), (.s7, .a6), (.s8, .t2)]

/-- `vg_mldsa*_verify_message` for the parameter set `p`, calling the
verification function on `μ` `f`, named `n`. -/
def verifyMessage (n : String) (f : Prog isa) (p : Params) : Prog isa :=
  top <| .seq (.block (enter .a6 p verifyRegs verifyMs)) <| .seq (trHash p) <|
  .seq (muHash ⟨.s8, oMU, .imm 64⟩) <|
  .seq (.seq (.block [mov .a0 .s0, .addi .a1 .s8 oMU, mov .a2 .s5, mov .a3 .s7]) (.call n f))
    (.block (restoreRegs .s8 oSV verifyRegs))

end VG.Impl.MlDsa.RISCV64.Message
