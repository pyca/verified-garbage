module

public import VerifiedGarbage.Proof.AesOcb.X86_64.AesNi.Top
public import VerifiedGarbage.Proof.AesOcb.X86_64.CTBase
public import VerifiedGarbage.Proof.AesOcb.X86_64.SealCT
import VerifiedGarbage.Proof.AesOcb.X86_64.CmpMask
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesOcb.X86_64.AesNi.Top
meta import VerifiedGarbage.Proof.AesOcb.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesOcb.X86_64.SealCT
meta import VerifiedGarbage.Proof.AesOcb.X86_64.CmpMask
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Callee

/-!
# One-pass AES-OCB with AES-NI on x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments are related piece by piece (`RelCT`), as for the functions over the
AES block functions (`SealCT.lean`): the entry (`entry_rel`), `Ktop`, `mid`
and the data with the tag, each by the taint analysis from the registers and
slots of `W` that correctness says agree (`ocbTN`, `BothN`): a copy loop
stores bytes the analysis cannot place, after which it forgets every slot, so
it starts again from what correctness says after each piece that has one.
Then, for `seal`, the copy of the tag and `restore` (`sealTail_relN`); for
`open`, the copy of the received tag, the comparison, the mask and
`restore`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64.AesNi

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxLstar)
open VG.Proof.AesOcb.X86_64 (LayN EnvN BufN DBufN ArgsN EntryPostN TwoN OneN BothN ocbTN rel_taintCN entry_rel
  Slots SealOutN sealTail_relN narrowTN rel_narrow readW_writeW_off)
open VG.Impl.AesOcb.X86_64 (tgO tlO tagO t2O alenO tmpO botO recv cmp mask restore ld entry)
open VG.Impl.AesOcb.X86_64AesNi (ktop mid body tag front imcO)

/-- Slots kept where the words at their offsets are. -/
theorem slots_of_eq {W : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {m m' : Mem}
    (S : Slots W R N A D nl n tl m)
    (h : ∀ d, (208 ≤ d ∧ d + 8 ≤ 248) ∨ (288 ≤ d ∧ d + 8 ≤ 304) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64) :
    Slots W R N A D nl n tl m' where
  data := by rw [h 208 (by decide)]; exact S.data
  len := by rw [h 216 (by decide)]; exact S.len
  tl := by rw [h 224 (by decide)]; exact S.tl
  rounds := by rw [h 232 (by decide)]; exact S.rounds
  aad := by rw [h 240 (by decide)]; exact S.aad
  nonce := by rw [h 288 (by decide)]; exact S.nonce
  nlen := by rw [h 296 (by decide)]; exact S.nlen

/-- What `ktop` leaves, from the state `entry` started from. -/
def KF (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) (wn : Nat) (s₀ t : State) : Prop :=
  ∃ σ, EntryPostN K W SP wn R N A D nl al n tl T s₀ σ ∧ KtopPost K W R tl (bytesAt σ.mem N nl) σ t

section
variable {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr} {wn : Nat}
  (Tw : TwoN s₀ s₀' K W SP N A D R nl al n tl T wn) (hwn : 640 ≤ wn) (hwlt : wn < 2 ^ 64)
  (hw : s₀.wr = [⟨D, n⟩, ⟨W, wn⟩]) (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, wn⟩])
include Tw hwn hwlt hw hw'

theorem kf_both {a b : State} (ha : KF K W SP N A D R nl al n tl T wn s₀ a)
    (hb : KF K W SP N A D R nl al n tl T wn s₀' b) :
    BothN K W SP R N A D nl n tl [.rdi, .rsi, .r10] [alenO] wn a b := by
  obtain ⟨σ, P, Kp⟩ := ha
  obtain ⟨σ', P', Kp'⟩ := hb
  have dk : ∀ d k, (208 ≤ d ∧ d + k ≤ 256) ∨ (288 ≤ d ∧ d + k ≤ 304) →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 botO, 8⟩],
        (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hd r hr
    have e1 : tmpO = 112 := rfl
    have e2 : botO = 256 := rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
  have kr : ∀ {σ t : State} {nb : List Byte}, KtopPost K W R tl nb σ t → ∀ d,
      (208 ≤ d ∧ d + 8 ≤ 256) ∨ (288 ≤ d ∧ d + 8 ≤ 304) →
      t.mem.readW (W + BitVec.ofNat 64 d) 64 = σ.mem.readW (W + BitVec.ofNat 64 d) 64 := fun K d hd =>
    K.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (dk d 8 hd) (by decide)
  have kenv : ∀ {σ t : State} {nb : List Byte}, EnvN K W SP wn σ → KtopPost K W R tl nb σ t → EnvN K W SP wn t :=
    fun E K => E.keep (fun r hr => K.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) K.rd K.wr
  have rdi₁ : a.gpr .rdi = K := by rw [Kp.gpr _ (by decide), P.rdi, Tw.di]
  have rdi₂ : b.gpr .rdi = K := by rw [Kp'.gpr _ (by decide), P'.rdi, Tw.di']
  refine ⟨kenv P.env Kp, kenv P'.env Kp', slots_of_eq P.slots fun d hd => kr Kp d (by omega_arith),
    slots_of_eq P'.slots fun d hd => kr Kp' d (by omega_arith), Kp.wr.trans (P.wr.trans hw),
    Kp'.wr.trans (P'.wr.trans hw'), fun r hr => ?_, fun d hd => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [rdi₁, rdi₂]
    · rw [Kp.rsi, Kp'.rsi]
    · rw [Kp.r10, Kp'.r10, P.rdi, P'.rdi, Tw.di, Tw.di']
  · simp only [List.mem_singleton] at hd; subst hd
    exact ⟨by simp only [alenO]; omega_arith, by
      rw [kr Kp alenO (by decide), kr Kp' alenO (by decide), P.alen, P'.alen]⟩

omit Tw hwn hwlt in
theorem mid_both {enc : Bool} {a b : State} (ha : MidPost enc K W SP N A D R nl al n tl T wn s₀ a)
    (hb : MidPost enc K W SP N A D R nl al n tl T wn s₀' b) :
    BothN K W SP R N A D nl n tl [.rdi, .rsi, .r10] [] wn a b := by
  refine ⟨ha.body.env, hb.body.env, ha.slots, hb.slots, ha.wr.trans hw, hb.wr.trans hw', fun r hr => ?_,
    fun _ h => (nomatch h)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [ha.body.rdi, hb.body.rdi]
  · rw [ha.body.rsi, hb.body.rsi]
  · rw [ha.body.r10, hb.body.r10, ha.body.rdi, hb.body.rdi]

/-- `front enc d` in two runs from states whose writable regions are the
data and `W`, given the taint analysis of its pieces after `entry`. -/
theorem front_relG (enc : Bool) (d : Nat) (hd' : d = 0 ∨ d = t2O) (hwo : enc = false → imcO + 224 ≤ wn)
    (hk : ∃ hc, (taint.check (ocbTN [.rdi] [] wn) ktop hc).isSome = true)
    (hm : ∃ hc, (taint.check (ocbTN [.rdi, .rsi, .r10] [alenO] wn) (mid enc) hc).isSome = true)
    (hb : ∃ hc, (taint.check (ocbTN [.rdi, .rsi, .r10] [] wn) (.seq (body enc) (tag d)) hc).isSome = true) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (front enc d) fun a b =>
      True ∧ FrontPost enc d K W SP N A D R nl al n tl T wn s₀ a ∧
        FrontPost enc d K W SP N A D R nl al n tl T wn s₀' b := by
  have L : LayN K W SP wn := Tw.ar.lay
  have hDW := Tw.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt Tw.ar.data.lt
  have hwn' : 304 ≤ wn := by omega_arith
  have hwlt' : wn ≤ 2 ^ 64 := by omega_arith
  have e := (entry_rel Tw).wp (F₁ := EntryPostN K W SP wn R N A D nl al n tl T s₀)
    (F₂ := EntryPostN K W SP wn R N A D nl al n tl T s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨TwoN.entry₁ Tw hwn hwlt, TwoN.entry₂ Tw hwn hwlt⟩
  have kt := (rel_taintCN [.rdi] [] hDW hn (P := fun a b => True ∧ EntryPostN K W SP wn R N A D nl al n tl T s₀ a ∧
      EntryPostN K W SP wn R N A D nl al n tl T s₀' b)
    (fun a b h => ⟨h.2.1.env, h.2.2.env, h.2.1.slots, h.2.2.slots, h.2.1.wr.trans hw, h.2.2.wr.trans hw',
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.rdi, h.2.2.rdi, Tw.di, Tw.di'],
      fun _ h => (nomatch h)⟩) hk hwn' hwlt').wp
    (F₁ := KF K W SP N A D R nl al n tl T wn s₀) (F₂ := KF K W SP N A D R nl al n tl T wn s₀')
    fun a b h => by
      obtain ⟨-, P, P'⟩ := h
      exact ⟨WP.mono (ktop_ok L P.env Tw.ar.rounds (P.rdi.trans Tw.di) P.slots.rounds P.slots.nonce P.slots.nlen
          P.slots.tl Tw.ar.n1 Tw.ar.n15 Tw.ar.tag.lt (Tw.ar.nonce.of_eq P.rd P.wr) hwn hwlt) fun t K => ⟨a, P, K⟩,
        WP.mono (ktop_ok Tw.ar'.lay P'.env Tw.ar'.rounds (P'.rdi.trans Tw.di') P'.slots.rounds P'.slots.nonce
          P'.slots.nlen P'.slots.tl Tw.ar'.n1 Tw.ar'.n15 Tw.ar'.tag.lt (Tw.ar'.nonce.of_eq P'.rd P'.wr) hwn hwlt)
          fun t K => ⟨b, P', K⟩⟩
  have mm := (rel_taintCN [.rdi, .rsi, .r10] [alenO] hDW hn
    (P := fun a b => True ∧ KF K W SP N A D R nl al n tl T wn s₀ a ∧ KF K W SP N A D R nl al n tl T wn s₀' b)
    (fun a b h => kf_both Tw hwn hwlt hw hw' h.2.1 h.2.2) hm hwn' hwlt').wp
    (F₁ := MidPost enc K W SP N A D R nl al n tl T wn s₀) (F₂ := MidPost enc K W SP N A D R nl al n tl T wn s₀')
    fun a b h => by
      obtain ⟨-, ⟨σ, P, K⟩, ⟨σ', P', K'⟩⟩ := h
      exact ⟨mid_ok enc Tw.ar hwn hwlt hwo Tw.di P K, mid_ok enc Tw.ar' hwn hwlt hwo Tw.di' P' K'⟩
  have bb := (rel_taintCN [.rdi, .rsi, .r10] [] hDW hn
    (P := fun a b => True ∧ MidPost enc K W SP N A D R nl al n tl T wn s₀ a ∧
      MidPost enc K W SP N A D R nl al n tl T wn s₀' b)
    (fun a b h => mid_both hw hw' h.2.1 h.2.2) hb hwn' hwlt').wp
    (F₁ := FrontPost enc d K W SP N A D R nl al n tl T wn s₀)
    (F₂ := FrontPost enc d K W SP N A D R nl al n tl T wn s₀')
    fun a b h => ⟨back_ok enc d hd' Tw.ar hwn hwlt h.2.1, back_ok enc d hd' Tw.ar' hwn hwlt h.2.2⟩
  unfold front
  exact RelCT.seq e (RelCT.seq kt (RelCT.seq mm bb))

end

/-! ## The taint analysis of the pieces -/

theorem ktop_t640 : ∃ hc, (taint.check (ocbTN [.rdi] [] 640) ktop hc).isSome = true := ⟨_, by taint_decide⟩

theorem mid_tSeal : ∃ hc, (taint.check (ocbTN [.rdi, .rsi, .r10] [alenO] 640) (mid true) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem back_tSeal :
    ∃ hc, (taint.check (ocbTN [.rdi, .rsi, .r10] [] 640) (.seq (body true) (tag 0)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ktop_t848 : ∃ hc, (taint.check (ocbTN [.rdi] [] 848) ktop hc).isSome = true := ⟨_, by taint_decide⟩

theorem mid_tOpen : ∃ hc, (taint.check (ocbTN [.rdi, .rsi, .r10] [alenO] 848) (mid false) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem back_tOpen :
    ∃ hc, (taint.check (ocbTN [.rdi, .rsi, .r10] [] 848) (.seq (body false) (tag t2O)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## `seal` -/

open VG.Proof.AesCcm.X86_64 (length_bytesAt) in
/-- `seal` in two runs. -/
theorem seal_rel {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Tw : TwoN s₀ s₀' K W SP N A D R nl al n tl T 640) (hw : s₀.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 640⟩])
    (hw' : s₀'.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 640⟩]) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') Impl.AesOcb.X86_64AesNi.seal fun _ _ => True := by
  have Tn := Tw.narrow hw hw'
  have inner := (front_relG Tn (by decide) (by decide) rfl rfl true tagO (.inl rfl) (fun h => absurd h (by decide))
      ktop_t640 mid_tSeal back_tSeal).mono (P' := fun σ₁ σ₂ => ∃ s₁ s₂,
      (s₁ = s₀ ∧ s₂ = s₀') ∧ σ₁ = s₁.withRegions (s₁.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 640⟩] ∧
        σ₂ = s₂.withRegions (s₂.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 640⟩])
    (fun _ _ ⟨_, _, ⟨rfl, rfl⟩, e₁, e₂⟩ => ⟨e₁, e₂⟩) fun _ _ h => h
  have cw : ∀ {s : State}, s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 640⟩] →
      Covers ([⟨T, tl⟩] ++ [⟨D, n⟩, ⟨W, 640⟩]) s.wr ∧ Covers [⟨D, n⟩, ⟨W, 640⟩] s.wr := fun h => by
    rw [h]
    refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  have fr := (rel_narrow [⟨T, tl⟩] [⟨D, n⟩, ⟨W, 640⟩] inner fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, _, e₁, -⟩ := front_ok true tagO (.inl rfl) Tn.ar (by decide) (by decide)
        (fun h => absurd h (by decide)) Tn.sp Tn.dd Tn.nn Tn.tg Tn.tt Tn.ww Tn.di Tn.si Tn.dx Tn.cx Tn.r8 Tn.r9
      obtain ⟨_, _, e₂, -⟩ := front_ok true tagO (.inl rfl) Tn.ar' (by decide) (by decide)
        (fun h => absurd h (by decide)) Tn.sp' Tn.dd' Tn.nn' Tn.tg' Tn.tt' Tn.ww' Tn.di' Tn.si' Tn.dx' Tn.cx'
        Tn.r8' Tn.r9'
      exact ⟨⟨(cw hw).1, (cw hw).2, _, _, e₁⟩, ⟨(cw hw').1, (cw hw').2, _, _, e₂⟩⟩).wp
    (F₁ := FrontPost true tagO K W SP N A D R nl al n tl T 640 s₀)
    (F₂ := FrontPost true tagO K W SP N A D R nl al n tl T 640 s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨front_ok true tagO (.inl rfl) Tw.ar (by decide) (by decide) (fun h => absurd h (by decide)) Tw.sp Tw.dd
          Tw.nn Tw.tg Tw.tt Tw.ww Tw.di Tw.si Tw.dx Tw.cx Tw.r8 Tw.r9,
        front_ok true tagO (.inl rfl) Tw.ar' (by decide) (by decide) (fun h => absurd h (by decide)) Tw.sp' Tw.dd'
          Tw.nn' Tw.tg' Tw.tt' Tw.ww' Tw.di' Tw.si' Tw.dx' Tw.cx' Tw.r8' Tw.r9'⟩
  unfold Impl.AesOcb.X86_64AesNi.seal
  exact RelCT.seq fr (sealTail_relN (wn := 640) fun a b h => ⟨⟨h.2.1.env, h.2.1.slots.tl, h.2.1.tg⟩,
    ⟨h.2.2.env, h.2.2.slots.tl, h.2.2.tg⟩⟩)

/-! ## `open` -/

section
variable {s₀ : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {Tg : Addr}
  (Ar : ArgsN s₀ K W SP N A D R nl al n tl Tg 848) (hw : s₀.wr = [⟨D, n⟩, ⟨W, 848⟩])
include Ar hw

open VG.Proof.AesCcm.X86_64 (length_bytesAt) in
/-- `recv` keeps the public arguments. -/
theorem recv_one {s : State} (F : FrontPost false t2O K W SP N A D R nl al n tl Tg 848 s₀ s) :
    WP isa recv s (OneN K W SP R N A D nl n tl 848) := by
  refine WP.mono (Proof.AesOcb.X86_64.recv_ok F.env Ar.t1 Ar.t16 F.tg F.slots.tl (Ar.tag.of_eq F.rd F.wr).rd Ar.tag.w)
    fun t ⟨m, g, rd, wr⟩ => ?_
  have fr : Frame [⟨W, tl⟩] s.mem t.mem := by
    rw [m]; exact WriteBytes.writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  refine ⟨F.env.keep g rd wr, slots_of_eq F.slots fun d hd =>
    fr.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base W (by have := Ar.t16; omega_arith) (by omega_arith)) (by decide),
    by rw [wr, F.wr, hw]⟩

omit hw in
/-- The comparison keeps the public arguments, and leaves 1 or 0 at `W`. -/
theorem cmp_one {s : State} (o : OneN K W SP R N A D nl n tl 848 s) :
    WP isa cmp s fun t => OneN K W SP R N A D nl n tl 848 t ∧
      ∃ c : Bool, t.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64 := by
  refine WP.mono (Proof.AesOcb.X86_64.cmp_ok o.env Ar.t1 Ar.t16 o.sl.tl) fun t ⟨m, g, rd, wr⟩ => ?_
  have E : EnvN K W SP 848 t := o.env.keep (fun r hr => g r
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd wr
  refine ⟨⟨E, slots_of_eq o.sl fun d hd => by
      rw [m, readW_writeW_off _ (by simp only [tagO]; omega_arith) (by omega_arith) (by decide)],
    by rw [wr, o.wr]⟩, decide (bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl), ?_⟩
  rw [m, Mem.readW_writeW_self64]; simp only [decide_eq_true_eq]

omit hw in
/-- The mask keeps the public arguments. -/
theorem mask_one {s : State} (o : OneN K W SP R N A D nl n tl 848 s) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) :
    WP isa mask s (OneN K W SP R N A D nl n tl 848) := by
  have hD : DBufN K W SP 848 s D n :=
    { toBufN := { Ar.data.toBufN with rd := Covers.right (by rw [o.wr]; exact Covers.of_mem fun r hr => by simp_all) }
      wr := by rw [o.wr]; exact Covers.of_mem fun r hr => by simp_all
      k := Ar.data.k }
  refine WP.mono (Proof.AesOcb.X86_64.mask_ok o.env o.sl.data o.sl.len hD hok) fun t ⟨E, _, wr, m⟩ => ?_
  have fr : Frame [⟨D, n⟩] s.mem t.mem := by
    rw [m]
    exact WriteBytes.writeBytes_frame _ _ _ (by rw [Proof.AesOcb.X86_64.length_mask]; exact Region.contains_self _ _)
  exact ⟨E, slots_of_eq o.sl fun d hd => fr.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Ar.data.w.sub_right (LayN.wSub (by omega_arith))).symm) (by decide), by rw [wr, o.wr]⟩

end

/-- `open` in two runs. -/
theorem open_rel {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {Tg : Addr}
    (Tw : TwoN s₀ s₀' K W SP N A D R nl al n tl Tg 848) (hw : s₀.wr = [⟨D, n⟩, ⟨W, 848⟩])
    (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, 848⟩]) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') Impl.AesOcb.X86_64AesNi.open fun _ _ => True := by
  have hDW := Tw.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt Tw.ar.data.lt
  have fr := front_relG Tw (by decide) (by decide) hw hw' false t2O (.inr rfl) (fun _ => by decide)
    ktop_t848 mid_tOpen back_tOpen
  have rr := (rel_taintCN [] [tgO] hDW hn (P := fun a b => True ∧
      FrontPost false t2O K W SP N A D R nl al n tl Tg 848 s₀ a ∧ FrontPost false t2O K W SP N A D R nl al n tl Tg 848 s₀' b)
    (fun a b h => ⟨h.2.1.env, h.2.2.env, h.2.1.slots, h.2.2.slots, h.2.1.wr.trans hw, h.2.2.wr.trans hw',
      fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd; exact ⟨by decide, by rw [h.2.1.tg, h.2.2.tg]⟩⟩)
    (c := recv) ⟨_, by taint_decide⟩).wp
    (F₁ := OneN K W SP R N A D nl n tl 848) (F₂ := OneN K W SP R N A D nl n tl 848)
    fun a b h => ⟨recv_one Tw.ar hw h.2.1, recv_one Tw.ar' hw' h.2.2⟩
  have cc := (rel_taintCN [] [] hDW hn (P := fun a b => True ∧ OneN K W SP R N A D nl n tl 848 a ∧
      OneN K W SP R N A D nl n tl 848 b) (fun a b h => BothN.of h.2.1 h.2.2) (c := cmp) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (s : State) => OneN K W SP R N A D nl n tl 848 s ∧
      ∃ c : Bool, s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64)
    (F₂ := fun (s : State) => OneN K W SP R N A D nl n tl 848 s ∧
      ∃ c : Bool, s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64)
    fun a b h => ⟨cmp_one Tw.ar h.2.1, cmp_one Tw.ar' h.2.2⟩
  have mm := (rel_taintCN [] [] hDW hn (P := fun a b => True ∧ (OneN K W SP R N A D nl n tl 848 a ∧
      ∃ c : Bool, a.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) ∧
    (OneN K W SP R N A D nl n tl 848 b ∧
      ∃ c : Bool, b.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64))
    (fun a b h => BothN.of h.2.1.1 h.2.2.1) (c := mask) ⟨_, by taint_decide⟩).wp
    (F₁ := OneN K W SP R N A D nl n tl 848) (F₂ := OneN K W SP R N A D nl n tl 848)
    fun a b h => ⟨mask_one Tw.ar h.2.1.1 h.2.1.2.choose_spec, mask_one Tw.ar' h.2.2.1 h.2.2.2.choose_spec⟩
  have rs := rel_taintCN [] [] hDW hn (P := fun a b => True ∧ OneN K W SP R N A D nl n tl 848 a ∧
    OneN K W SP R N A D nl n tl 848 b) (fun a b h => BothN.of h.2.1 h.2.2)
    (c := .block ([ld .rax .r15 tagO] ++ restore)) ⟨_, by taint_decide⟩
  unfold Impl.AesOcb.X86_64AesNi.open
  exact RelCT.seq fr (RelCT.seq rr (RelCT.seq cc (RelCT.seq mm rs)))

end VG.Proof.AesOcb.X86_64.AesNi
