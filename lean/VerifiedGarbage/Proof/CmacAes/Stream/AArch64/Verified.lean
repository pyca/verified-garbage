import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Init
import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Finish
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.AbsorbCorrect

section

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to values of the public arguments
(`AMid₁`, `AAfter₁`, `AMid₂`, `AAfter₂`), and each call of
`vg_cmac_aes_update` is constant time by its own proof (`upd_rel`).
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (agree_of)

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₁ s₀ St D S L R s) :
    WP isa (.call v.callee.name v.callee.code) s
      (AAfter₁ s₀ St D S L) :=
  WP.mono (upd_call v _ h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved .x19 (by simp [preserved]) (by decide), h.x19],
      by rw [h₆.saved .x20 (by simp [preserved]) (by decide), h.x20],
      by rw [h₆.saved .x21 (by simp [preserved]) (by decide), h.x21],
      by rw [h₆.saved .x22 (by simp [preserved]) (by decide), h.x22],
      by rw [h₆.saved .x23 (by simp [preserved]) (by decide), h.x23],
      by rw [h₆.sp, h.sp], by rw [h₆.rd, h.rd], by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)) S R
    (nbOf (s₀.gpr .x2).toNat L)
  x19 : s.gpr .x19 = St
  x24 : s.gpr .x24 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .x2).toNat L)
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp

theorem chain2_mid {s₀ s : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
    (h : AAfter₁ s₀ St D S L s) : WP isa chain2 s (AMid₂ s₀ St D S L R) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .x2).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le c L
  have hsum := nb_le c L
  obtain ⟨x19₆, x20₆, x21₆, x22₆, x23₆, sp₆, rd₆, wr₆⟩ := h
  rw [hc] at x21₆ x22₆
  refine WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega) x22₆) fun s₇ h₇ => ?_
  obtain ⟨x24₇, x4₇, x0₇, x1₇, x2₇, x3₇, x5₇, sv₇, sp₇, -, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x24₇ x4₇
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  subst hc
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L), 16 * nbOf (s₀.gpr .x2).toNat L⟩
      ⟨D, L⟩ := Offset.sub_base D (by omega)
  refine ⟨hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L))
    (n := nbOf (s₀.gpr .x2).toNat L)
    (by rw [x0₇, x19₆]) (by rw [x1₇, x20₆]) (by rw [x2₇, x19₆]) (by rw [x3₇, x21₆]) x4₇
    (by rw [x5₇, x23₆]) (by rw [rd₇, rd₆]) (by rw [wr₇, wr₆]) (by omega) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf (s₀.gpr .x2).toNat L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)).isLt; omega
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega)]; omega)
    ⟨⟨D, L⟩, by simp, fOf (s₀.gpr .x2).toNat L, rfl, by simp; omega⟩,
    by rw [sv₇ .x19 (by simp [preserved]) (by decide), x19₆], x24₇,
    by rw [sv₇ .x21 (by simp [preserved]) (by decide), x21₆],
    by rw [sv₇ .x22 (by simp [preserved]) (by decide), x22₆],
    by rw [sv₇ .x23 (by simp [preserved]) (by decide), x23₆], by rw [sp₇, sp₆]⟩

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x24 : s.gpr .x24 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .x2).toNat L)
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp

theorem call2_after (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₂ s₀ St D S L R s) :
    WP isa (.call v.callee.name v.callee.code) s
      (AAfter₂ s₀ St D S L) :=
  WP.mono (upd_call v _ h.args) fun _ h₈ =>
    ⟨by rw [h₈.saved .x19 (by simp [preserved]) (by decide), h.x19],
      by rw [h₈.saved .x24 (by simp [preserved]) (by decide), h.x24],
      by rw [h₈.saved .x21 (by simp [preserved]) (by decide), h.x21],
      by rw [h₈.saved .x22 (by simp [preserved]) (by decide), h.x22],
      by rw [h₈.saved .x23 (by simp [preserved]) (by decide), h.x23], by rw [h₈.sp, h.sp]⟩

theorem absorb_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ s₀' : State} (h0 : absorbAArch64.pre s₀) (h0' : absorbAArch64.pre s₀')
    (hq : absorbAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat := by
    rw [q0, q1, q3, q4, q5]; exact APre.of h0'
  generalize s₀.gpr .x0 = St at hp hp'
  generalize s₀.gpr .x3 = D at hp hp'
  generalize s₀.gpr .x5 = S at hp hp'
  generalize (s₀.gpr .x4).toNat = L at hp hp'
  generalize (s₀.gpr .x1).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) absorbPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) chain2 h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x21, .x22, .x23, .x24]) absorbPost h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q6 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := AMid₁ s₀ St D S L R) (F₂ := AMid₁ s₀' St D S L R) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absorbPre_wp hp, absorbPre_wp hp'⟩
  have c₁ := (upd_rel v _ (P := fun a b => AMid₁ s₀ St D S L R a ∧ AMid₁ s₀' St D S L R b)
    fun a b h => ⟨h.1.args, by rw [q2]; exact h.2.args, by rw [h.1.sp, h.2.sp, q6]⟩).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h => ⟨call1_after v h.1, call1_after v h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q6]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x20, h.2.x20, q1]
      · rw [h.1.x21, h.2.x21, q2]
      · rw [h.1.x22, h.2.x22, q2]
      · rw [h.1.x23, h.2.x23]) hB).wp
    (F₁ := AMid₂ s₀ St D S L R) (F₂ := AMid₂ s₀' St D S L R) fun a b h => ⟨chain2_mid hp h.1, chain2_mid hp' h.2⟩
  have c₂ := (upd_rel v _ (P := fun a b => AMid₂ s₀ St D S L R a ∧ AMid₂ s₀' St D S L R b)
    fun a b h => ⟨h.1.args, by rw [q2]; exact h.2.args, by rw [h.1.sp, h.2.sp, q6]⟩).wp
    (F₁ := AAfter₂ s₀ St D S L) (F₂ := AAfter₂ s₀' St D S L) fun a b h =>
      ⟨call2_after v h.1, call2_after v h.2⟩
  have p := RelCT.taint (A := taint) (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q6]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x21, h.2.x21, q2]
      · rw [h.1.x22, h.2.x22, q2]
      · rw [h.1.x23, h.2.x23]
      · rw [h.1.x24, h.2.x24, q2]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem absorb_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa absorbAArch64.pre absorbAArch64.pub (absorb v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.AArch64

end

/-!
# Streaming AES-CMAC on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of AES), a state
satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with no stack: the calls keep the return address in
`x30`, which each function saves in the scratch buffer).
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (update_keepsV subkeys_keepsV finalize_keepsV)

theorem init_keepsV (v : Ctr32Impl) : (init v.expand v.callee v.suffix).allInstrs keepsV = true := by
  simp only [init, Code.allInstrs, v.expandKeepsV, subkeys_keepsV v]; decide +kernel

theorem absorb_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) : (absorb v.callee).allInstrs keepsV = true := by
  simp only [absorb, absorbPre, absorbPost, held, clamp, fill, copy, chain1, chain2, Code.allInstrs,
    v.keepsV]
  decide +kernel

theorem finish_keepsV (v : Ctr32Impl) : (finish v.callee v.suffix).allInstrs keepsV = true := by
  simp only [finish, finPre, lastLen, Code.allInstrs, finalize_keepsV v]; decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (init_wp v hs) (init_keepsV v)

theorem absorb_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : absorbAArch64.pre s) :
    ∃ t s', Exec isa (absorb v.callee) s t s' ∧ abiPreserved s s' ∧ absorbAArch64.post s s' :=
  WP.withPreservedV (absorb_wp v hs) (absorb_keepsV v)

theorem finish_correct (v : Ctr32Impl) (s : State) (hs : finishAArch64.pre s) :
    ∃ t s', Exec isa (finish v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ finishAArch64.post s s' :=
  WP.withPreservedV (finish_wp v hs) (finish_keepsV v)

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 16 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified AArch64.target (init v.expand v.callee v.suffix) (Spec.Cmac.aesInitContract AArch64.abi) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, initAArch64, AArch64.abi,
      AArch64.argRegs] [initSat] using initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x3 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target (absorb v.callee) (Spec.Cmac.aesAbsorbContract AArch64.abi) :=
  Verified.of_correct (absorb_correct v) (absorb_ct v) (by
    sig_implies [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, absorbAArch64, AArch64.abi,
      AArch64.argRegs] [absorbSat] using absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x3 => 0x2000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified (v : Ctr32Impl) :
    Verified AArch64.target (finish v.callee v.suffix) (Spec.Cmac.aesFinishContract AArch64.abi) :=
  Verified.of_correct (finish_correct v) (finish_ct v) (by
    sig_implies [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, finishAArch64, AArch64.abi,
      AArch64.argRegs] [finishSat] using finishSat)

end VG.Proof.CmacAes.Stream.AArch64
