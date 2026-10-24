module

import VerifiedGarbage.Proof.Dsa.Arm.Gen.Frame
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.St
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP

/-! # DSA parameter generation on ARMv7: copies from the tapes

`copyR_vp`: `n` bytes from an address a frame word holds (a seed, an `h`)
into `scratch`. `GI.tapeBytes`: the tapes keep their bytes through the
search, which writes only the frame, `scratch` and the stack below.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_movw wp_mov wp_dp op2_reg op2_imm dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP}

theorem copyBytes_cert :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr]) VG.Impl.Bignum.Arm.copyBytes hc).isSome = true :=
  ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1, .lr]) VG.Impl.Bignum.Arm.copyBytes, rfl⟩

/-- A copy by `copyBytes`, from `src` to `dst`, with its pointers and length known. -/
theorem copyBytes_vp {P Q : State → State → Prop} {src dst : BitVec 32} {n : Nat}
    (hp : ∀ σ s, P σ s → s.gpr .r1 = src ∧ s.gpr .r0 = dst ∧ s.gpr .lr = BitVec.ofNat 32 n)
    (wp : ∀ σ s, P σ s → WP isa VG.Impl.Bignum.Arm.copyBytes s (Q σ)) :
    VP P VG.Impl.Bignum.Arm.copyBytes Q :=
  VP.taint [.r0, .r1, .lr] copyBytes_cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
    obtain ⟨a₁, b₁, c₁⟩ := hp _ _ h₁
    obtain ⟨a₂, b₂, c₂⟩ := hp _ _ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [a₁, a₂]
    · rw [c₁, c₂]) wp

/-- `n` bytes from the address `x` in the frame word `o`, readable and apart
from `scratch`, to `scratch + dst`. -/
theorem copyR_vp {P Q : State → State → Prop} {c : State → Cfg} {L dst n o : Nat} {x : BitVec 32}
    (hF : ∀ σ s, P σ s → SS G σ (c σ) s) (hL : L = G.pLen) (ho : o + 4 ≤ F + 32) (h4 : o % 4 = 0)
    (hx : ∀ σ s, P σ s → fw s.mem G o = x) (hn : 0 < n) (hn16 : n < 2 ^ 16) (hd : dst + n ≤ sK L)
    (hsrc : ∀ σ s, P σ s → InRegions s.rd (State.addr x) n ∧ Region.Disjoint ⟨State.addr x, n⟩ G.rScr ∧
      x.toNat + n ≤ 2 ^ 32)
    (k : ∀ σ s t, P σ s → Rest [.r0, .r1, .r2, .r12, .lr] s t → Frame [G.rs dst n] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem (State.addr x) n → Q σ t) :
    VP P (copyN (scr L .r0 dst) [ld .r1 o] n) Q := by
  -- After the pointers and the count.
  let P₂ : State → State → Prop := fun σ t => ∃ s, P σ s ∧ Rest [.r0, .r1, .r12, .lr] s t ∧ t.mem = s.mem ∧
    t.gpr .r1 = x ∧ t.gpr .r0 = G.scr + BitVec.ofNat 32 dst ∧ t.gpr .lr = BitVec.ofNat 32 n
  simp only [copyN, List.append_assoc]
  refine VP.seq (G := P₂) (VP.block_append (G := fun σ t => ∃ s, P σ s ∧ Upd s t .r1 x)
    (ld_vp hF ho h4 hx fun σ s t hs u => ⟨s, hs, u⟩) ?_) ?_
  · refine VP.taint [.r1, .r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1, .r8])
        (.block (scr 128 .r0 0 ++ [.movw .lr (BitVec.ofNat 16 5)])), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ ⟨_, h₁, u₁⟩ ⟨_, h₂, u₂⟩ r hr => ?_) fun σ t ⟨s, hs, u⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [u₁.gpr, u₂.gpr]
      · rw [u₁.other _ (by decide), u₂.other _ (by decide), (hF _ _ h₁).r8, (hF _ _ h₂).r8]
    have h := hF σ s hs
    have big := h.gi.scrBig
    subst hL
    refine scr_ok (d := .r0) (by rw [u.other _ (by decide)]; exact h.r8) rfl h.lens (by omega)
      fun s₁ v₁ R₁ M₁ => wp_movw fun s₂ u₂ => WP.block_nil
        ⟨s, hs, ((u.rest (by simp)).trans (R₁.mono (by simp))).trans (u₂.rest (by simp)),
          by rw [u₂.mem, M₁, u.mem], by rw [u₂.other _ (by decide), R₁.gpr _ (by decide), u.gpr],
          by rw [u₂.other _ (by decide)]; exact v₁, ?_⟩
    rw [u₂.gpr]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  refine copyBytes_vp (src := x) (dst := G.scr + BitVec.ofNat 32 dst) (n := n)
    (fun σ t ⟨_, _, _, _, a, b, c⟩ => ⟨a, b, c⟩) fun σ s₂ ⟨s, hs, R, M, v1, v0, vl⟩ => ?_
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  obtain ⟨rd, dj, xf⟩ := hsrc σ s hs
  subst hL
  have ad := h.addr hd hn
  refine WP.mono (VG.Proof.Bignum.Arm.copyBuffer_ok s₂ (src := x) (dst := G.scr + BitVec.ofNat 32 dst) hn xf
    (by rw [h.toNat (by omega)]; omega) (by omega)
    (by rw [R.rd]; obtain ⟨r, hr, hc⟩ := rd; exact ⟨r, List.mem_append_left _ hr, hc⟩)
    (by rw [ad, R.wr]; exact gi.inScr (by omega))
    (by rw [ad]; exact dj.sub_right (sw G (by omega))) v0 v1 vl)
    fun t' ⟨rd', fr, _, rest⟩ => k σ s t' hs ((R.mono (by simp)).trans (rest.mono (by simp)))
      (by rw [← M]; show Frame [⟨G.sa dst, n⟩] _ _; rw [← ad]; exact fr) ?_
  rw [← ad, ← M]; exact bytesAt_of_read rd'

/-- A slice of bytes. -/
theorem bytesAt_slice' (m : Mem) (p : Addr) {k n len : Nat} (h : k + n ≤ len) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) n = ((Spec.Rsa.bytesAt m p len).drop k).take n := by
  obtain ⟨r, rfl⟩ : ∃ r, len = k + (n + r) := ⟨len - k - n, by omega⟩
  rw [VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.drop_left' (bytesAt_length' _ _ _),
    List.take_left' (bytesAt_length' _ _ _)]

/-- A range the search does not write keeps its bytes. -/
theorem GI.keeps {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS s) {p : BitVec 32}
    {len : Nat} (hfit : p.toNat + len ≤ 2 ^ 32) (hd : ∀ r ∈ G.chg, Region.Disjoint ⟨State.addr p, len⟩ r) {k n : Nat}
    (hk : k + n ≤ len) :
    Spec.Rsa.bytesAt s.mem (State.addr (p + BitVec.ofNat 32 k)) n =
      ((Spec.Rsa.bytesAt σ.mem (State.addr p) len).drop k).take n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Spec.Rsa.bytesAt]
  rw [addr_add (by omega), ← bytesAt_slice' σ.mem _ hk]
  exact VG.Proof.Dsa.Generation.frame_bytesAt h.frame (fun r hr => (hd r hr).sub_left
    (Offset.sub_base _ (by omega))) (by omega)

/-- The tapes are apart from what the search writes. -/
theorem GI.tape_apart {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS s) {R : Region}
    (hst : R.Disjoint (rStack σ)) (hsc : R.Disjoint G.rScr) : ∀ r ∈ G.chg, R.Disjoint r := fun r hr => by
  simp only [GP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hst.sub_right h.frameSub
  · exact hsc
  · exact hst.sub_right h.belowSub

theorem GI.seeds_apart {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS s) :
    ∀ r ∈ G.chg, G.rSeeds.Disjoint r := by
  have a := h.pre.fS; have b := h.pre.sC; rw [h.hG] at a b
  exact h.tape_apart a.symm b

theorem GI.hs_apart {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS s) :
    ∀ r ∈ G.chg, G.rHs.Disjoint r := by
  have a := h.pre.fH; have b := h.pre.hC; rw [h.hG] at a b
  exact h.tape_apart a.symm b

theorem GI.wit_apart {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS s) :
    ∀ r ∈ G.chg, G.rWit.Disjoint r := by
  have a := h.pre.fW; have b := h.pre.wC; rw [h.hG] at a b
  exact h.tape_apart a.symm b

end

end VG.Proof.Dsa.Arm.Gen
