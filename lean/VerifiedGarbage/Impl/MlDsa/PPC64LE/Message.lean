module

public import VerifiedGarbage.Impl.Sha3.PPC64LE.Pieces
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Arith
public import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA on PPC64LE: `vg_mldsa{44,65,87}_sign_message` and `_verify_message`

`sign_message(sk = r3, msg = r4, msg_len = r5, ctx = r6, ctx_len = r7,
rnd = r8, sig = r9, scratch = r10) -> r3` and `verify_message(pk = r3,
msg = r4, msg_len = r5, ctx = r6, ctx_len = r7, sig = r8, scratch = r9) -> r3`:
`ML-DSA.Sign` and `ML-DSA.Verify` (FIPS 204 Algorithms 2 and 3), as calls of
the sponge functions (`hash`, `Impl/Sha3/PPC64LE/Pieces.lean`) and of the
functions on `μ` (`vg_mldsa*_sign`, `vg_mldsa*_verify`), named `n` and with
the code `f`.

If `ctx_len ≥ 256` (`ctx_len >> 8 ≠ 0`) they return 2 at once. Otherwise
they work in the 1 KiB after the working space of the function on `μ` (at
`oE p`, from `scratch`; its address `E` is kept in `r30`): the Keccak state
(200 bytes) and the sponge functions' working space (640 bytes), the 840
bytes `hash` uses; `μ` (64 bytes); our caller's registers that we use and
the link register (`saveRegs`, at `oSV`); and the two bytes `0 ‖ ctx_len` of
the formatted message (at `oHdr`). They use no stack of their own. The
arguments stay in `r22`–`r29`, which the functions called keep.

* Signing computes `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, with `tr` the 64
  bytes of `sk` at 64, and calls `vg_mldsa*_sign(sk, μ, rnd, sig, scratch)`.
* Verification first computes `tr = H(pk, 64)` into the buffer of `μ`, then
  `μ` from it likewise, and calls `vg_mldsa*_verify(pk, μ, sig, scratch)`.

Every address and branch depends only on the pointers and the lengths, and
the calls' own leakage.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Message

open VG.PPC64LE
open VG.Spec.MlDsa (Params)
open VG.Impl.Sha3.PPC64LE.Pieces (Piece hash)
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Impl.Ed25519.PPC64LE.Whole (saveRegs restoreRegs)

/-- Where the 1 KiB starts in `scratch`: after the working space of the
functions on `μ`. -/
def oE (p : Params) : Nat := 8 * Spec.MlDsa.scratchWords p

/-! ## The 1 KiB, from `E` -/

/-- The bytes `hash` uses (the Keccak state, then the sponge functions'
working space). -/
def nK : Nat := 840
/-- `μ`. -/
def oMU : Nat := 840
/-- Our caller's registers and the link register. -/
def oSV : Nat := 904
/-- The two bytes of the formatted message. -/
def oHdr : Nat := 984

/-! ## Entry and exit -/

/-- `0 ‖ ctx_len` (`ctx_len` in `r26`) at `oHdr`. -/
def hdr : List Instr := [.li .r0 0, .stb .r0 .r30 oHdr, .stb .r26 .r30 (oHdr + 1)]

/-- `E` (`scratch` in `sr` plus `oE p`) in `r12`. -/
def base (sr : Reg) (p : Params) : List Instr :=
  Impl.MlDsa.PPC64LE.Arith.loadImm .r12 (oE p) ++ ([.add .r12 sr .r12] : List Instr)

/-- `E` in `r12`, our caller's registers `rs` and the link register saved
there, and the moves `ms` (to, from) of the arguments. -/
def enter (sr : Reg) (p : Params) (rs : List Reg) (ms : List (Reg × Reg)) : List Instr :=
  base sr p ++ (saveRegs .r12 oSV rs ++ ms.map (fun m => mov m.1 m.2) ++ hdr)

/-- The formatted message after its first piece: `0 ‖ ctx_len`, the
context (`r25`, `r26`), the message (`r23`, `r24`). -/
def fmtPieces : List Piece := [⟨.r30, oHdr, .imm 2⟩, ⟨.r25, 0, .reg .r26⟩, ⟨.r23, 0, .reg .r24⟩]

/-- `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, for the 64 bytes `tr` at `tr`. -/
def muHash (tr : Piece) : Prog isa := hash .r30 (tr :: fmtPieces) .r30 oMU 64

/-- `tr = H(pk, 64)` (`pk` in `r22`) to the buffer of `μ`. -/
def trHash (p : Params) : Prog isa := hash .r30 [⟨.r22, 0, .imm p.pkLen⟩] .r30 oMU 64

/-- If `ctx_len < 256`, `body`; otherwise return 2. -/
def top (body : Prog isa) : Prog isa :=
  .seq (.block [.lsr .d .r11 .r7 8]) (.ite (.zero .d .r11) body (.block [.li .r3 2]))

/-! ## The functions -/

/-- The registers signing uses: `sk`, `msg`, `msg_len`, `ctx`, `ctx_len`,
`rnd`, `sig`, `scratch` and `E` (the base of the saves, last). -/
def signRegs : List Reg := [.r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30]

def signMs : List (Reg × Reg) :=
  [(.r22, .r3), (.r23, .r4), (.r24, .r5), (.r25, .r6), (.r26, .r7), (.r27, .r8), (.r28, .r9), (.r29, .r10),
    (.r30, .r12)]

/-- `vg_mldsa*_sign_message` for the parameter set `p`, calling the signing
function on `μ` `f`, named `n`. -/
def signMessage (n : String) (f : Prog isa) (p : Params) : Prog isa :=
  top <| .seq (.block (enter .r10 p signRegs signMs)) <| .seq (muHash ⟨.r22, 64, .imm 64⟩) <|
  .seq (.seq (.block [mov .r3 .r22, .addi .r4 .r30 oMU, mov .r5 .r27, mov .r6 .r28, mov .r7 .r29]) (.call n f))
    (.block (restoreRegs .r30 oSV signRegs))

/-- The registers verification uses: `pk`, `msg`, `msg_len`, `ctx`,
`ctx_len`, `sig`, `scratch` and `E`. -/
def verifyRegs : List Reg := [.r22, .r23, .r24, .r25, .r26, .r27, .r29, .r30]

def verifyMs : List (Reg × Reg) :=
  [(.r22, .r3), (.r23, .r4), (.r24, .r5), (.r25, .r6), (.r26, .r7), (.r27, .r8), (.r29, .r9), (.r30, .r12)]

/-- `vg_mldsa*_verify_message` for the parameter set `p`, calling the
verification function on `μ` `f`, named `n`. -/
def verifyMessage (n : String) (f : Prog isa) (p : Params) : Prog isa :=
  top <| .seq (.block (enter .r9 p verifyRegs verifyMs)) <| .seq (trHash p) <|
  .seq (muHash ⟨.r30, oMU, .imm 64⟩) <|
  .seq (.seq (.block [mov .r3 .r22, .addi .r4 .r30 oMU, mov .r5 .r27, mov .r6 .r29]) (.call n f))
    (.block (restoreRegs .r30 oSV verifyRegs))

end VG.Impl.MlDsa.PPC64LE.Message
