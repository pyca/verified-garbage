module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateStage
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT

/-! # The CRT's key check and factor preparation, as parameters

The private CRT (`CrtFn.codeOf`) checks the key with `check` and prepares
each factor in the narrow workspace with `prime`: `vg_rsa_private_crt`'s
are `CrtFn.validate` and `narrowPrime`. Its proofs take any that do what
those do, for the keys `ok` holds of: `vg_rsa_private_crt_precomputed`'s
take the factors' `R² mod p` from the key's precomputed values, and need
not check `p q = n`, which those values imply. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

/-- What preparing a factor (`narrowPrime`) leaves. -/
def NarrowPrimePost (base : BitVec 32) (len v : Nat) (pb : List Byte) (s t : State) : Prop :=
  ArithmeticReady base len v t ∧
    numAt t.mem (State.addr base) v 0 =
      safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (Spec.Rsa.os2ip pb) ∧
    safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (Spec.Rsa.os2ip pb) % 2 = 1 ∧
    numAt t.mem (State.addr base) v 4 =
      2 ^ (128 * v) % safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (Spec.Rsa.os2ip pb) ∧
    t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
    Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t

/-- The factor `j.succ` (p or q), to be prepared in the narrow workspace. -/
def CrtPrimeIn (g : CrtGeometry) (bs : Fin 7 → List Byte) (j : Fin 6) (s : State) : Prop :=
  CrtShared g bs s ∧ NarrowPrimeInput (crtN g.base g.words) (g.source j.succ) (workspaceWords g.words)
    (narrowWords (g.sourceLength j.succ) g.words) (g.sourceLength j.succ) (56 + 8 * j.val) (bs j.succ) s

/-- What checking the key (`CrtFn.validate`) leaves. -/
def CrtCheckPost (g : CrtGeometry) (bs : Fin 7 → List Byte) (s t : State) : Prop :=
  CrtShared g bs t ∧ LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
    numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
    numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
    t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) ∧
    Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t

structure CrtStages where
  check : Prog isa
  prime : Nat → Prog isa
  /-- The keys the stages are for. -/
  ok : CrtGeometry → (Fin 7 → List Byte) → Prop
  checkOk : ∀ {g : CrtGeometry} {bs : Fin 7 → List Byte} (s : State), ok g bs → CrtShared g bs s →
    LayoutFrameReady g.base (workspaceWords g.words) g.words s → WP isa check s (CrtCheckPost g bs s)
  checkCt : ∀ {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte}, ok g bs1 → ok g bs2 →
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      check (fun _ _ => True)
  primeOk : ∀ {g : CrtGeometry} {bs : Fin 7 → List Byte} (j : Fin 6) (s : State), j = 1 ∨ j = 2 → ok g bs →
    CrtPrimeIn g bs j s →
    WP isa (prime (56 + 8 * j.val)) s (NarrowPrimePost (crtN g.base g.words) (workspaceWords g.words)
      (narrowWords (g.sourceLength j.succ) g.words) (bs j.succ) s)
  primeCt : ∀ {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (j : Fin 6), j = 1 ∨ j = 2 → ok g bs1 → ok g bs2 →
    RelCT isa (fun s t => CrtPrimeIn g bs1 j s ∧ CrtPrimeIn g bs2 j t ∧ s.sp = t.sp)
      (prime (56 + 8 * j.val)) (fun _ _ => True)

end VG.Proof.Bignum.Arm
