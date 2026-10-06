import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
import VerifiedGarbage.Proof.RsaPss.AArch64.RelSplit

/-!
# RSASSA-PSS on AArch64: `mgfXor` is constant time

Two runs of `mgfXor` with the same frame, working space and `DB` (its place
`e` and length `db`, public) leak the same trace (`mgfXor_ct`): each round's
pieces are checked by the taint analysis from registers the anchor fixes
(`MR`), the digest by `mgfHash_ct`, the load of `done` (public, `c hLen`) at
the start of `xorOut` is related by correctness, and the rounds go the same
way in both runs (`round_ok`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_strx eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map wp_ldrSp wp_addSp)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-- What two runs of `mgfXor` share. -/
structure MA where
  F : Addr
  S : Addr
  e : Nat
  db : Nat

/-- A run in round `p.2`, with registers (`rs`) and slots (`sl`) the anchor
fixes. -/
structure MR (D : Nat) (rs : List (Reg × (MA × Nat → BitVec 64))) (sl : List (Nat × (MA × Nat → BitVec 64)))
    (p : MA × Nat) (u : State) : Prop where
  L : Lay u p.1.F p.1.S
  r : ∀ q ∈ rs, u.gpr q.1 = q.2 p
  s : ∀ q ∈ sl, u.mem.readW (off p.1.F q.1) 64 = q.2 p
  hd : DbAt D p.1.e p.1.db
  hc : p.2 * D < p.1.db

theorem MR.pins {D : Nat} {rs : List (Reg × (MA × Nat → BitVec 64))} {sl : List (Nat × (MA × Nat → BitVec 64))}
    {qs : List Reg} (h : ∀ r ∈ qs, r = .x20 ∨ ∃ f, (r, f) ∈ rs) : Pins (MR D rs sl) qs :=
  fun p s₁ s₂ h₁ h₂ => by
    refine ⟨by rw [h₁.L.sp, h₂.L.sp], fun r hr => ?_⟩
    rcases h r hr with rfl | ⟨f, hf⟩
    · rw [h₁.L.x20, h₂.L.x20]
    · rw [h₁.r _ hf, h₂.r _ hf]

/-- The registers of a round: `st`, the digest, `DB`, `dbLen` and the counter. -/
def mregs : List (Reg × (MA × Nat → BitVec 64)) :=
  [(.x19, fun p => off p.1.S oSt), (.x21, fun p => off p.1.S oDig), (.x24, fun p => off p.1.S p.1.e),
    (.x25, fun p => BitVec.ofNat 64 p.1.db), (.x28, fun p => BitVec.ofNat 64 p.2)]

/-- `done`. -/
def mslots (D : Nat) : List (Nat × (MA × Nat → BitVec 64)) := [(sDone, fun p => BitVec.ofNat 64 (p.2 * D))]

/-- `MR` after code that keeps the registers of `rs` and writes only `ws`,
apart from the slots of `sl`. -/
theorem MR.keep {D : Nat} {rs : List (Reg × (MA × Nat → BitVec 64))} {sl : List (Nat × (MA × Nat → BitVec 64))}
    {p : MA × Nat} {u u' : State} (h : MR D rs sl p u) {ks : List Reg} (k : Keep ks u u')
    (hk : ∀ q ∈ rs, q.1 ∉ ks) (h20 : Reg.x20 ∉ ks) {ws : List Region} (hf : Frame ws u.mem u'.mem)
    (hs : ∀ q ∈ sl, ∀ r ∈ ws, Region.Disjoint (slotR p.1.F q.1) r) : MR D rs sl p u' where
  L := h.L.congr k.sp k.wr (k.gpr .x20 h20)
  r := fun q hq => by rw [k.gpr q.1 (hk q hq)]; exact h.r q hq
  s := fun q hq => by rw [slot_keep hf (hs q hq)]; exact h.s q hq
  hd := h.hd
  hc := h.hc

theorem done_S {D : Nat} {F S : Addr} {t : State} (L : Lay t F S) :
    ∀ q ∈ mslots D, ∀ r ∈ [(⟨S, oRsa⟩ : Region)], Region.Disjoint (slotR F q.1) r := by
  intro q hq r hr
  simp only [mslots, List.mem_singleton] at hq
  subst hq
  rw [List.mem_singleton.mp hr]
  exact L.dFS.sub_left (Offset.sub_base F (d := sDone) (by decide))

section
variable {H : Hash} (hH : HashOK H)

include hH in
theorem clearBlock_mct :
    RelCT isa (Two (MR H.D mregs (mslots H.D))) (clearBlock H) (Two (MR H.D mregs (mslots H.D))) :=
  two_post (two_taintE [.x20] (MR.pins fun r hr => by simp at hr; exact .inl hr)
      (c' := Code.eraseOff (clearBlock zH)) rfl (by taint_decide))
    fun _ _ h => WP.mono (clearBlock_ok hH h.L (fun _ _ => rfl)) fun _ ⟨k, f, _⟩ =>
      h.keep k (by decide) (by decide) f (done_S h.L)

include hH in
theorem copyH_mct :
    RelCT isa (Two (MR H.D mregs (mslots H.D))) (copyH H) (Two (MR H.D mregs (mslots H.D))) :=
  two_post (two_taintE [.x20, .x24, .x25] (MR.pins fun r hr => by
        simp at hr; rcases hr with rfl | rfl | rfl <;> simp [mregs])
      (c' := Code.eraseOff (copyH zH)) rfl (by taint_decide))
    fun p _ h => WP.mono (copyH_ok hH h.L (fun _ _ => rfl) h.hd
      (h.r (.x24, fun p => off p.1.S p.1.e) (by simp [mregs]))
      (h.r (.x25, fun p => BitVec.ofNat 64 p.1.db) (by simp [mregs]))) fun _ ⟨k, f, _⟩ => h.keep k (by decide) (by decide) f (done_S h.L)

/-- After the counter: its message's length, and its number of blocks. -/
def mregs2 (H : Hash) : List (Reg × (MA × Nat → BitVec 64)) :=
  mregs ++ [(.x22, fun _ => BitVec.ofNat 64 (H.D + 4))]
def mslots2 (H : Hash) : List (Nat × (MA × Nat → BitVec 64)) :=
  mslots H.D ++ [(sNb, fun _ => BitVec.ofNat 64 (mgfNb H))]

include hH in
theorem counter_mct :
    RelCT isa (Two (MR H.D mregs (mslots H.D))) (.block (counter H)) (Two (MR H.D (mregs2 H) (mslots2 H))) := by
  refine two_post (two_taintE [.x20, .x28] (MR.pins fun r hr => by
        simp at hr; rcases hr with rfl | rfl <;> simp [mregs])
      (c' := Code.eraseOff (.block (counter zH))) rfl (by taint_decide)) fun p u h => ?_
  have hD := hH.sizes.D0
  have hc := h.hc
  have hfit := h.hd.fit
  have : p.2 ≤ p.2 * H.D := Nat.le_mul_of_pos_right _ hD
  refine WP.mono (counter_ok hH h.L (fun _ _ => rfl) (c := p.2) (h.r (.x28, fun p => BitVec.ofNat 64 p.2)
    (by simp [mregs])) (by unfold oY at hfit; omega)) fun u' ⟨k, x22, nb, fr, _⟩ => ?_
  have h' := h.keep k (by decide) (by decide) fr fun q hq r hr => by
    simp only [mslots, List.mem_singleton] at hq
    subst hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show Region.Disjoint (slotR _ sDone) r
    rcases hr with rfl | rfl
    · exact h.L.dFS.sub_left (Offset.sub_base _ (d := sDone) (by decide))
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  refine ⟨h'.L, fun q hq => ?_, fun q hq => ?_, h.hd, h.hc⟩
  · rcases List.mem_append.mp hq with hq | hq
    · exact h'.r q hq
    · rw [List.mem_singleton.mp hq]; exact x22
  · rcases List.mem_append.mp hq with hq | hq
    · exact h'.s q hq
    · rw [List.mem_singleton.mp hq]; exact nb

include hH in
theorem mgfHash_mct (hc : PssChecks H.P H.D) :
    RelCT isa (Two (MR H.D (mregs2 H) (mslots2 H))) (mgfHash H) (Two (MR H.D mregs (mslots H.D))) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  obtain ⟨hnb1, hnb, _⟩ := mgfNb_spec hH
  refine two_post (two_map (fun p => (⟨p.1.F, p.1.S, mgfNb H, some (H.D + 4)⟩ : HA)) (fun p u h => ⟨{
      L := h.L
      x19 := h.r (.x19, fun p => off p.1.S oSt) (by simp [mregs2, mregs])
      x21 := h.r (.x21, fun p => off p.1.S oDig) (by simp [mregs2, mregs])
      nb := h.s (sNb, fun _ => BitVec.ofNat 64 (mgfNb H)) (by simp [mslots2])
      len := ⟨H.D + 4, h.r (.x22, fun _ => BitVec.ofNat 64 (H.D + 4)) (by simp [mregs2]), hnb1⟩
      hnb := by show mgfNb H * H.P.B ≤ 2048; omega
      fx := fun ℓ e => by
        simp only [Option.some.injEq] at e
        subst e
        exact h.r (.x22, fun _ => BitVec.ofNat 64 (H.D + 4)) (by simp [mregs2]) }, rfl⟩)
    (mgfHash_ct hH hc)) fun p u h => ?_
  have x22 := h.r (.x22, fun _ => BitVec.ofNat 64 (H.D + 4)) (by simp [mregs2])
  refine WP.mono (ctHashWith_out hH _ h.L (fun _ _ => rfl) (h.r (.x19, fun p => off p.1.S oSt) (by simp [mregs2, mregs]))
    (h.r (.x21, fun p => off p.1.S oDig) (by simp [mregs2, mregs])) x22
    (h.s (sNb, fun _ => BitVec.ofNat 64 (mgfNb H)) (by simp [mslots2])) hnb1 (by omega) fun L' R' _ _ => ?_)
    fun u' O => ?_
  · exact WP.mono (fixedPad_ok L' R' (n := mgfNb H * H.P.B) (by omega) (by unfold oY; omega)) fun _ ⟨k, f, r⟩ =>
      ⟨k.mono, f, r⟩
  refine ⟨h.L.congr O.sp O.wr (O.cs .x20 (by decide)), fun q hq => ?_, fun q hq => ?_, h.hd, h.hc⟩
  · have hq2 : q ∈ mregs2 H := List.mem_append_left _ hq
    rw [← h.r q hq2]
    simp only [mregs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact O.cs _ (by decide)
  · have hq2 : q ∈ mslots2 H := List.mem_append_left _ hq
    rw [← h.s q hq2]
    simp only [mslots, List.mem_singleton] at hq
    subst hq
    refine slot_keep O.fr fun r hr => ?_
    show Region.Disjoint (slotR _ sDone) r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.L.dFS.sub_left (Offset.sub_base _ (d := sDone) (by decide))
    · exact slot_not_below _ (by decide)

include hH in
theorem xorOut_mct :
    RelCT isa (Two (MR H.D mregs (mslots H.D))) (xorOut H) (Two (MR H.D mregs (mslots H.D))) := by
  refine two_post ?_ fun p u h => ?_
  · unfold xorOut seqs seqs
    refine RelCT.seq_block_append (M := isa) (l₁ := [ld .x9 sDone]) ?_
    refine RelCT.seq (two_post (Ψ := MR H.D (mregs ++ [(.x9, fun p => BitVec.ofNat 64 (p.2 * H.D))]) (mslots H.D))
      (two_taint [] (MR.pins fun _ h => absurd h List.not_mem_nil) (by taint_decide)) fun p u h => ?_) ?_
    · unfold ld
      refine wp_ldrSp (by decide) (by rw [h.L.sp]; exact h.L.fld (by decide)) fun u' o e => wp_nil ?_
      have h' := h.keep o.keep (by decide) (by decide) (by rw [o.mem]; exact Frame.refl _ _)
        (ws := []) fun _ _ _ h => absurd h List.not_mem_nil
      refine ⟨h'.L, fun q hq => ?_, h'.s, h.hd, h.hc⟩
      rcases List.mem_append.mp hq with hq | hq
      · exact h'.r q hq
      · rw [List.mem_singleton.mp hq, e, h.L.sp]; exact h.s (sDone, fun p => BitVec.ofNat 64 (p.2 * H.D)) (by simp [mslots])
    · exact two_taintE [.x9, .x21, .x24, .x25] (MR.pins fun r hr => by
          simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> simp [mregs])
        (c' := Code.eraseOff (.seq (.block [.add .x .x10 .x24 .x9, Impl.MdStream.AArch64.mov .x11 .x21,
            .sub .x .x12 .x25 .x9, movi .x13 zH.D, .sub .x .x14 .x12 .x13, .lsr .x .x14 .x14 63])
          (.seq (.ite (.zero .x .x14) (.block [Impl.MdStream.AArch64.mov .x12 .x13]) (.block []))
            (.loop (.block [.ldrb .x9 .x11 0, .ldrb .x15 .x10 0, .logic .eor .x .x15 .x15 .x9, .strb .x15 .x10 0,
              .addImm .x .x11 .x11 1, .addImm .x .x10 .x10 1, .subImm .x .x12 .x12 1]) (.nonzero .x .x12)))))
        rfl (by taint_decide)
  · exact WP.mono (xorOut_ok hH h.L (fun _ _ => rfl) h.hd (h.r (.x24, fun p => off p.1.S p.1.e) (by simp [mregs]))
      (h.r (.x25, fun p => BitVec.ofNat 64 p.1.db) (by simp [mregs]))
      (h.r (.x21, fun p => off p.1.S oDig) (by simp [mregs]))
      (h.s (sDone, fun p => BitVec.ofNat 64 (p.2 * H.D)) (by simp [mslots])) h.hc)
      fun _ ⟨k, f, _⟩ => h.keep k (by decide) (by decide) f (done_S h.L)

theorem nextCtr_mct : RelCT isa (Two (MR H.D mregs (mslots H.D))) (.block (nextCtr H)) fun _ _ => True :=
  two_taintE [] (MR.pins fun _ h => absurd h List.not_mem_nil) (c' := Code.eraseOff (.block (nextCtr zH))) rfl
    (by taint_decide)

/-- `mgfXor`'s start, with the anchor's frame, working space and `DB`. -/
structure MS (D : Nat) (a : MA) (t : State) : Prop where
  L : Lay t a.F a.S
  hd : DbAt D a.e a.db
  x19 : t.gpr .x19 = off a.S oSt
  x21 : t.gpr .x21 = off a.S oDig
  x24 : t.gpr .x24 = off a.S a.e
  x25 : t.gpr .x25 = BitVec.ofNat 64 a.db

/-- In round `p.2` of `mgfXor`, from a start `t` (`MgfI`). -/
def MI (G : Spec.Mgf1.Hash) (D : Nat) (p : MA × Nat) (u : State) : Prop :=
  ∃ t V, MS D p.1 t ∧ MgfI t p.1.F p.1.S V (Spec.Mgf1.mgf1 G ((List.range D).map fun i => V (p.1.e + p.1.db + i))
    p.1.db) p.1.e p.1.db D p.2 u ∧ p.2 * D < p.1.db

theorem MI.mr {G : Spec.Mgf1.Hash} {D : Nat} {p : MA × Nat} {u : State} (h : MI G D p u) :
    MR D mregs (mslots D) p u := by
  obtain ⟨t, V, hs, I, hc⟩ := h
  refine ⟨hs.L.congr I.sp I.wr (I.cs .x20 (by decide)), fun q hq => ?_, fun q hq => ?_, hs.hd, hc⟩
  · simp only [mregs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [I.cs .x19 (by decide)]; exact hs.x19
    · rw [I.cs .x21 (by decide)]; exact hs.x21
    · rw [I.cs .x24 (by decide)]; exact hs.x24
    · rw [I.cs .x25 (by decide)]; exact hs.x25
    · exact I.x28
  · simp only [mslots, List.mem_singleton] at hq
    subst hq
    exact I.done

include hH in
theorem mgfXor_ct {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) (hc : PssChecks H.P H.D) :
    RelCT isa (Two (MS H.D)) (mgfXor H) fun _ _ => True := by
  have hD := hH.sizes.D0
  have c2 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold mgfXor
  refine RelCT.seq (two_post (Ψ := fun a u => MI G H.D (a, 0) u)
    (two_taint [] (fun a s₁ s₂ h₁ h₂ => ⟨by rw [h₁.L.sp, h₂.L.sp], fun _ h => absurd h List.not_mem_nil⟩)
      (by taint_decide)) fun a t h => ?_) ?_
  · unfold st movi
    simp only [List.cons_append, List.nil_append]
    refine wp_movz fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_addSp (by decide) fun u₃ o₃ e₃ => ?_
    refine wp_strx (by decide) (by rw [e₃, o₂.sp, o₁.sp, h.L.sp, BitVec.add_zero])
      (by rw [o₃.wr, o₂.wr, o₁.wr]; exact h.L.fst (by decide)) fun v m₄ => wp_nil ?_
    have hm : v.mem = t.mem.writeW (off a.F sDone) (0#64) := by
      rw [m₄.mem, o₃.get .x9, e₂, o₃.mem, o₂.mem, o₁.mem]; rfl
    have K : Keep [.x28, .x9, .x16] t v := (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans m₄.keep))).mono
    refine ⟨t, fun o => v.mem (off a.S o), h, ⟨K.sp, K.rd, K.wr, fun r hr => K.gpr r ?_, K.vcs, ?_, ?_, ?_,
      fun o ho₁ ho₂ => ?_⟩, by show 0 * H.D < a.db; rw [Nat.zero_mul]; exact h.hd.db1⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [m₄.gpr, o₃.get .x28, o₂.get .x28, e₁]; rfl
    · rw [hm, Mem.readW_writeW_self64, Nat.zero_mul]
    · rw [hm]; exact (frame_slot _ a.F sDone _).mono (by simp)
    · simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]
      rw [ite_eq_right (by omega)]
  refine RelCT.exists_ fun a => ?_
  let I : Nat → State → State → Prop := fun n => Two fun p u => MI G H.D p u ∧ n = p.1.db - p.2 * H.D
  refine (RelCT.loop (Q := fun _ _ => True) I (fun n => ?_) (a.db - 0 * H.D)).mono
    (fun s₁ s₂ ⟨h₁, h₂⟩ => ⟨(a, 0), ⟨h₁, rfl⟩, h₂, rfl⟩) fun _ _ h => h
  have tr : RelCT isa (Two (MR H.D mregs (mslots H.D)))
      (seqs [clearBlock H, copyH H, .block (counter H), mgfHash H, xorOut H, .block (nextCtr H)])
      fun _ _ => True := by
    unfold seqs seqs seqs seqs seqs
    exact RelCT.seq (clearBlock_mct hH) (RelCT.seq (copyH_mct hH) (RelCT.seq (counter_mct hH)
      (RelCT.seq (mgfHash_mct hH hc) (RelCT.seq (xorOut_mct hH) nextCtr_mct))))
  have T : RelCT isa (I n) _ _ := two_post (Ψ := fun p u => (∃ t V, MS H.D p.1 t ∧
      MgfI t p.1.F p.1.S V (Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (p.1.e + p.1.db + i)) p.1.db)
        p.1.e p.1.db H.D (p.2 + 1) u) ∧
      (u.gpr .x10 != 0) = decide ((p.2 + 1) * H.D < p.1.db) ∧ n = p.1.db - p.2 * H.D)
    (tr.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.mr, h₂.1.mr⟩) fun _ _ h => h) fun p u ⟨h, hn⟩ => by
      obtain ⟨t, V, hs, Ig, hcd⟩ := h
      exact WP.mono (round_ok hH hGh hGl hG hs.L hs.hd hs.x19 hs.x21 hs.x24 hs.x25 Ig hcd)
        fun u' ⟨hx, I'⟩ => ⟨⟨t, V, hs, I'⟩, hx, hn⟩
  refine T.mono (fun _ _ h => h) fun s₁ s₂ ⟨⟨a', c⟩, ⟨m₁, x₁, hn⟩, m₂, x₂, _⟩ => ?_
  dsimp only at m₁ m₂ x₁ x₂ hn
  have ev : ∀ {u : State}, (u.gpr .x10 != 0) = decide ((c + 1) * H.D < a'.db) →
      isa.eval (.nonzero .x .x10) u = some (decide ((c + 1) * H.D < a'.db)) := fun hx => by
    rw [eval_nonzero, hx]
  refine ⟨by rw [ev x₁, ev x₂], fun _ => trivial, fun hc => ?_⟩
  rw [ev x₁, Option.some.injEq, decide_eq_true_eq] at hc
  have hs1 : (c + 1) * H.D = c * H.D + H.D := Nat.succ_mul _ _
  obtain ⟨t₁, V₁, hs₁, I₁⟩ := m₁
  obtain ⟨t₂, V₂, hs₂, I₂⟩ := m₂
  exact ⟨a'.db - (c + 1) * H.D, by omega, (a', c + 1), ⟨⟨t₁, V₁, hs₁, I₁, hc⟩, rfl⟩, ⟨t₂, V₂, hs₂, I₂, hc⟩, rfl⟩

end

end VG.Proof.RsaPss.AArch64
