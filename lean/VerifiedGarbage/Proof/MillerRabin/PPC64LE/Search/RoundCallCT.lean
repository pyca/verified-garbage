module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# A prime search on PPC64LE: the round's call in constant time

`roundCall_ct`: two runs from the same prepared working space and witness
(`RC`) leak the same: the witness into Montgomery form and the arguments
from the working space's registers, the round as its contract makes it
(`RelCT.call`), and the registers back.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Search

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.Bignum (slot)

/-- A round's call: the working space, the modulus and the witness. -/
structure RcD where
  B : Addr
  L : Nat
  w : Nat
  c : Nat
  a : Nat

/-- Before the call of a witness's round. -/
def RC (d : RcD) (s : State) : Prop :=
  Prep s d.B d.L d.w d.c ∧ arr s.mem d.B d.w 4 = d.a ∧ d.a < d.c ∧ 176 ≤ s.sp.toNat ∧ (below s.sp 176).Disjoint ⟨d.B, 8 * d.L⟩

/-- With the arguments in `r3` and `r4`. -/
def RCm (d : RcD) (s : State) : Prop :=
  Prep s d.B d.L d.w d.c ∧ val32 s.mem d.B (slot d.w 5) (2 * d.w) = d.a % d.c * 2 ^ (64 * d.w) % d.c ∧
    s.gpr .r3 = d.B ∧ s.gpr .r4 = BitVec.ofNat 64 d.L ∧
    176 ≤ s.sp.toNat ∧ (below s.sp 176).Disjoint ⟨d.B, 8 * d.L⟩

theorem pins_RC : Pins RC [.r10, .r11, .r29, .r31] := by
  rintro d s₁ s₂ ⟨h₁, -⟩ ⟨h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.env.h10, h₂.env.h10]
  · rw [h₁.env.h11, h₂.env.h11]
  · rw [h₁.env.h29, h₂.env.h29]
  · rw [h₁.env.h31, h₂.env.h31]

theorem rcPre_ok {d : RcD} {s : State} (h : RC d s) :
    WP isa (.seq (.seq (.block minv32) (PublicChecked.montOp 5 4 1)) (.block [.addi .r3 .r31 0, ldh .r4 hWsLen]))
      s (RCm d) := by
  obtain ⟨hp, ha, hac, hsp, hstk⟩ := h
  have e := hp.env
  have l56 : InRegions (s.rd ++ s.wr) (d.B + BitVec.ofNat 64 56) 8 := e.hs.ld (d := 56) (by
    have := e.hZ; simp only [slot, hdrBytes] at this; omega_arith)
  refine WP.assoc' (WP.seq (WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = (word s.mem d.B 56 <<< 32) >>> 32 ∧
      u.mem = s.mem) (by simp only [minv32, ldh, hMinv]; prun [e.h31, l56]) (by decide))
    fun u ⟨⟨u12, um⟩, ku⟩ => ?_))
  have hu : Prep u d.B d.L d.w d.c := hp.transfer (e.keep ku (by decide)) (fun d _ _ => by rw [um])
    (fun j _ _ => by rw [um])
  refine WP.mono (rcHead_ok hu (by rw [um]; exact u12) (by rw [um]; exact ha) hac) fun t m => ?_
  have k := ku.trans m.keep
  exact ⟨m.prep, m.a5, m.r3, m.r4, by rw [k.sp]; exact hsp, by rw [k.sp]; exact hstk⟩

theorem rcPre_ct : RelCT isa (Two RC)
    (.seq (.seq (.block minv32) (PublicChecked.montOp 5 4 1)) (.block [.addi .r3 .r31 0, ldh .r4 hWsLen]))
    (Two RCm) :=
  two_post (two_taint _ pins_RC (by taint_decide)) fun _ _ h => rcPre_ok h

/-- The round's precondition on its entry, from `RCm`. -/
theorem rc_pre {d : RcD} {s : State} (h : RCm d s) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 176).pre
      (s.callEntry.withRegions [] [⟨d.B, 8 * d.L⟩]) := by
  obtain ⟨p₂, h5, r3₂, r4₂, hsp, hstk⟩ := h
  have e := p₂.env
  have hnw := e.hs.nowrap
  have hL64 : d.L < 2 ^ 64 := by omega_arith
  sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [r3₂, r4₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL64, Nat.mul_comm d.L 8]
  exact ⟨hsp, trivial, hstk, by omega_arith, p₂.layout, p₂.prepared (by
    show val32 s.mem d.B (slot d.w 5) (2 * d.w) < d.c; rw [h5]; exact Nat.mod_lt _ (by have := p₂.c3; omega_arith))⟩

theorem rc_pub {d : RcD} {s₁ s₂ : State} (h₁ : RCm d s₁) (h₂ : RCm d s₂) (hsp : s₁.sp = s₂.sp) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 176).pub
      (s₁.callEntry.withRegions [] [⟨d.B, 8 * d.L⟩]) (s₂.callEntry.withRegions [] [⟨d.B, 8 * d.L⟩]) := by
  sig_reduce [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, PPC64LE.abi, PPC64LE.argRegs]
  obtain ⟨p₁, -, a3, a4, -⟩ := h₁
  obtain ⟨p₂, -, b3, b4, -⟩ := h₂
  rw [a3, a4, b3, b4, p₁.width, p₂.width]
  exact ⟨⟨hsp, rfl⟩, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

theorem rc_covers {s : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) :
    Covers ([] ++ [⟨B, 8 * L⟩]) (s.rd ++ s.wr) := fun x n hx => by
  obtain ⟨r, hr, hc⟩ := scr_covers h.env.hs (by simpa only [List.nil_append] using hx)
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- After the call: the working space's address. -/
def RCc (d : RcD) (s : State) : Prop := s.gpr .r31 = d.B

theorem rcCall_ct (R : RoundImpl) : RelCT isa (Two RCm) (.call R.name R.code) (Two RCc) := by
  refine two_post ?_ fun d s h => ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨d, h₁, h₂, hsp⟩ := hp
    have cov : ∀ {s : State}, RCm d s → Covers ([] ++ [⟨d.B, 8 * d.L⟩]) (s.rd ++ s.wr) ∧
        Covers [⟨d.B, 8 * d.L⟩] s.wr := fun h => ⟨rc_covers h.1, fun _ _ => scr_covers h.1.env.hs⟩
    exact RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) R.verified.1 R.verified.2.1 [] [⟨d.B, 8 * d.L⟩]
      (fun a b ⟨ha, hb⟩ => by
        subst ha hb
        exact ⟨rc_pre h₁, rc_pre h₂, rc_pub h₁ h₂ hsp, (cov h₁).1, (cov h₁).2, (cov h₂).1, (cov h₂).2⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  · have h31 := h.1.env.h31
    exact WP.callAny (k := Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 176) R.verified.1
      (rd := []) (wr := [⟨d.B, 8 * d.L⟩]) (rc_pre h) (rc_covers h.1) (fun _ _ => scr_covers h.1.env.hs)
      (fun s' _ _ _ _ hcs _ => (hcs .r31 (by decide)).trans h31) (by have := R.stack; omega_arith)

theorem pins_RCc : Pins RCc [.r31] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁, h₂]

/-- The round's call leaks the same from the same working space and witness. -/
theorem roundCall_ct (R : RoundImpl) : RelCT isa (Two RC) (roundCall R.name R.code) fun _ _ => True := by
  unfold roundCall
  refine RelCT.assoc (RelCT.assoc (RelCT.seq rcPre_ct (RelCT.seq (rcCall_ct R) ?_)))
  exact two_taint _ pins_RCc (by taint_decide)

end VG.Proof.MillerRabin.PPC64LE.Search
