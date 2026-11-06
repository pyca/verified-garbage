module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSAES-OAEP on x86-64: MGF1 in constant time

Two runs of `mgfXor lay G` with the same frame, regions, `src` and `dst`
(`MQ`): the frame's public slots in a round (`RW`, `RW.words`), where MGF1
starts (`ME`), and the number of rounds (`nR`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs round xorOut nextCtr initArgs updSrcArgs updCtrArgs finArgs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post two_map two_loop)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

/-- MGF1's public data: the frame, the working space, the other two writable
regions, and `src` and `dst` in the working space. -/
structure MQ where
  F : Addr
  S : Addr
  ws : List Region
  src : Nat
  srcLen : Nat
  dst : Nat
  dstLen : Nat

/-- The frame's words MGF1 reads, with the counter `c`. -/
def mw (D : Nat) (q : MQ) (c k : Nat) : BitVec 64 :=
  if k = 14 then q.S else if k = 15 then off q.S q.src else if k = 16 then BitVec.ofNat 64 q.srcLen
  else if k = 17 then off q.S q.dst else if k = 18 then BitVec.ofNat 64 q.dstLen
  else if k = 19 then BitVec.ofNat 64 c else BitVec.ofNat 64 (c * D)

/-- A point of the round with counter `c`. -/
structure RW (n D : Nat) (q : MQ) (c : Nat) (t : State) : Prop where
  fv : FrV n q.F q.ws t
  L : Lay t q.F q.S
  fit : MFit q.src q.srcLen q.dst q.dstLen
  lt : c * D < q.dstLen
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ MArgs W q.S q.src q.srcLen q.dst q.dstLen ∧
    W 19 = BitVec.ofNat 64 c ∧ W 20 = BitVec.ofNat 64 (c * D)

theorem RW.words {n D : Nat} {q : MQ} {c : Nat} {t : State} (h : RW n D q c t) :
    FrV n q.F q.ws t ∧ ∀ k ∈ [14, 15, 16, 17, 18, 19, 20], word t.mem q.F (8 * k) = mw D q c k := by
  obtain ⟨V, W, R, A, h19, h20⟩ := h.rep
  refine ⟨h.fv, fun k hk => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (slot_eq sScr 14 rfl _ _).symm.trans h.L.slot
  · rw [R.fr 15 (by decide), A.hsrc]; rfl
  · rw [R.fr 16 (by decide), A.hsl]; rfl
  · rw [R.fr 17 (by decide), A.hdst]; rfl
  · rw [R.fr 18 (by decide), A.hdl]; rfl
  · rw [R.fr 19 (by decide), h19]; rfl
  · rw [R.fr 20 (by decide), h20]; rfl

theorem RW.congr {n D : Nat} {q : MQ} {c : Nat} {t t' : State} (h : RW n D q c t) (hsp : t'.gpr .rsp = t.gpr .rsp)
    (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem) : RW n D q c t' :=
  ⟨h.fv.congr hsp hwr, h.L.congr hsp hwr (by rw [hm]), h.fit, h.lt, by rw [hm]; exact h.rep⟩

/-- After a piece that keeps the regions, with the slots as they were. -/
theorem RW.after {n D : Nat} {q : MQ} {c : Nat} {t t' : State} (h : RW n D q c t) (L' : Lay t' q.F q.S)
    (hwr : t'.wr = t.wr) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t'.mem q.F q.S V W)
    (A : MArgs W q.S q.src q.srcLen q.dst q.dstLen) (h19 : W 19 = BitVec.ofNat 64 c)
    (h20 : W 20 = BitVec.ofNat 64 (c * D)) : RW n D q c t' :=
  ⟨h.fv.congr (L'.rsp.trans h.L.rsp.symm) hwr, L', h.fit, h.lt, V, W, R, A, h19, h20⟩

variable {G : Stream} (hG : StreamOK G) (n : Nat)

/-! ## The points of a round -/

/-- A hash function's streaming functions of `hLen = d`, for the code that
depends on `hLen` alone. -/
def gD (d : Nat) : Stream := ⟨0, 0, d, 0, 0, "", .block [], "", .block [], "", .block []⟩

theorem nopin {β : Type} {Φ : β → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => absurd h List.not_mem_nil

/-! ## MGF1 -/

/-- Where MGF1 starts: in the frame, with its slots set. -/
structure ME (q : MQ) (t : State) : Prop where
  fv : FrV n q.F q.ws t
  L : Lay t q.F q.S
  fit : MFit q.src q.srcLen q.dst q.dstLen
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ MArgs W q.S q.src q.srcLen q.dst q.dstLen

/-- The number of rounds. -/
def nR (D : Nat) (q : MQ) : Nat := (q.dstLen + D - 1) / D

theorem lt_nR {D : Nat} (hD : 0 < D) (q : MQ) (j : Nat) : j < nR D q ↔ j * D < q.dstLen := by
  unfold nR
  rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le hD, Nat.succ_mul]
  omega

end VG.Proof.RsaOaep.X86_64
