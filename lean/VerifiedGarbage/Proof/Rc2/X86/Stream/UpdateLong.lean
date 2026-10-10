import VerifiedGarbage.Proof.Rc2.X86.Stream.Contract

section

section

/-!
# Streaming RC2-CBC on x86 (32-bit): the update functions' precondition

Names for the arguments and regions of an update (`Pre`), and what holds from
the saving of our caller's registers on (`Common`): the arguments are never
written, so they can be read at any point (`wp_arg`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp

theorem ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev ctx : BitVec 32 := arg s₀ 0
abbrev p : Nat := (arg s₀ 1).toNat
abbrev dp : BitVec 32 := arg s₀ 2
abbrev len : Nat := (arg s₀ 3).toNat
abbrev op : BitVec 32 := arg s₀ 4
abbrev O : Nat := (arg s₀ 5).toNat
abbrev scr : BitVec 32 := arg s₀ 6
abbrev cA : Addr := (ctx s₀).setWidth 64
abbrev dA : Addr := (dp s₀).setWidth 64
abbrev oA : Addr := (op s₀).setWidth 64
abbrev sA : Addr := (scr s₀).setWidth 64
abbrev ctxR : Region := ⟨cA s₀, 144⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev oR : Region := ⟨oA s₀, O s₀⟩
abbrev scR : Region := ⟨sA s₀, 576⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 40
/-- The pending block. -/
abbrev pendR : Region := ⟨cA s₀ + BitVec.ofNat 64 136, 8⟩
/-- The schedule and the chaining value. -/
abbrev schR : Region := ⟨cA s₀, 128⟩
abbrev ivR : Region := ⟨cA s₀ + BitVec.ofNat 64 128, 8⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [ctxR s₀, oR s₀, scR s₀]
  c_d : (ctxR s₀).Disjoint (dR s₀)
  c_o : (ctxR s₀).Disjoint (oR s₀)
  c_s : (ctxR s₀).Disjoint (scR s₀)
  d_o : (dR s₀).Disjoint (oR s₀)
  d_s : (dR s₀).Disjoint (scR s₀)
  o_s : (oR s₀).Disjoint (scR s₀)
  a_c : (argR s₀).Disjoint (ctxR s₀)
  a_o : (argR s₀).Disjoint (oR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  r_c : (retR s₀).Disjoint (ctxR s₀)
  r_o : (retR s₀).Disjoint (oR s₀)
  r_s : (retR s₀).Disjoint (scR s₀)
  k_c : (stkR s₀).Disjoint (ctxR s₀)
  k_d : (stkR s₀).Disjoint (dR s₀)
  k_o : (stkR s₀).Disjoint (oR s₀)
  k_s : (stkR s₀).Disjoint (scR s₀)
  c_fit : (ctx s₀).toNat + 144 ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  o_fit : (op s₀).toNat + O s₀ ≤ 2 ^ 32
  s_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 40 ≤ (E s₀).toNat
  sp_fit : (E s₀).toNat + 32 ≤ 2 ^ 32
  p_lt : p s₀ < 8
  O_eq : O s₀ = (p s₀ + len s₀) / 8 * 8

theorem pre_of {d : Spec.Rc2.Direction} {s₀ : State} (h : (updateContract d).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem argAddr_eq (i : Nat) (hi : i < 7) :
    addr (E s₀) (4 + 4 * i) = (E s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
  have := hp.sp_fit; exact addr_eq (by omega_arith)

theorem arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨addr (E s₀) (4 + 4 * i), 4⟩ (argR s₀) := by
  show Region.Sub _ ⟨addr (E s₀) (4 + 4 * 0), 28⟩
  rw [hp.argAddr_eq i hi, hp.argAddr_eq 0 (by decide)]
  exact Offset.sub _ (by omega_arith) (by omega_arith)

omit hp in
theorem pend_sub : Region.Sub (pendR s₀) (ctxR s₀) := Offset.sub_base _ (by decide)
omit hp in
theorem sch_sub : Region.Sub (schR s₀) (ctxR s₀) := Region.sub_prefix (by decide)
omit hp in
theorem iv_sub : Region.Sub (ivR s₀) (ctxR s₀) := Offset.sub_base _ (by decide)

omit hp in
theorem sch_pend : (schR s₀).Disjoint (pendR s₀) := Offset.base_disjoint _ (by decide) (by decide)
omit hp in
theorem iv_pend : (ivR s₀).Disjoint (pendR s₀) := Offset.disjoint _ (by decide) (by decide) (by decide)
omit hp in
theorem sch_iv : (schR s₀).Disjoint (ivR s₀) := Offset.base_disjoint _ (by decide) (by decide)

/-- A word of the scratch space. -/
theorem scr_addr {d : Nat} (hd : d + 4 ≤ 576) : addr (scr s₀) d = sA s₀ + BitVec.ofNat 64 d := by
  have := hp.s_fit; exact addr_eq (by omega_arith)

theorem scr_sub {d : Nat} (hd : d + 4 ≤ 576) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [hp.scr_addr hd]; exact Offset.sub_base _ hd

theorem sin {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hwr, hp.wr], by rw [hp.scr_addr hd]; exact Offset.contains_base _ hd (by omega_arith)⟩

theorem rin {s : State} (hrd : s.rd = s₀.rd) {i : Nat} (hi : i < 7) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [hrd, hp.rd], ?_⟩
  show (⟨addr (E s₀) (4 + 4 * 0), 28⟩ : Region).Contains _ _
  rw [hp.argAddr_eq i hi, hp.argAddr_eq 0 (by decide)]
  exact Offset.contains _ (by omega_arith) (by omega_arith) (by have := hp.sp_fit; omega_arith)

/-- The regions written are disjoint from the arguments, the saved words, the
schedule and the chaining value. -/
theorem sep_pend : ∀ r ∈ [argR s₀, scR s₀, schR s₀, ivR s₀, dR s₀, oR s₀, retR s₀, stkR s₀],
    r.Disjoint (pendR s₀) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact hp.a_c.sub_right Pre.pend_sub
  · exact (hp.c_s.sub_left Pre.pend_sub).symm
  · exact Pre.sch_pend
  · exact Pre.iv_pend
  · exact (hp.c_d.sub_left Pre.pend_sub).symm
  · exact (hp.c_o.sub_left Pre.pend_sub).symm
  · exact hp.r_c.sub_right Pre.pend_sub
  · exact hp.k_c.sub_right Pre.pend_sub

end Pre

/-! ## From the saving of our caller's registers on -/

structure Common (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  edi : s.gpr .edi = s₀.gpr .edi
  ebp : s.gpr .ebp = s₀.gpr .ebp
  frame : Frame [pendR s₀, oR s₀, scR s₀] s₀.mem s.mem
  ebx : s.mem.readW (addr (scr s₀) 512) 32 = s₀.gpr .ebx
  esi : s.mem.readW (addr (scr s₀) 516) 32 = s₀.gpr .esi

theorem Common.arg {s₀ s : State} (hp : Pre s₀) (h : Common s₀ s) {i : Nat} (hi : i < 7) :
    s.mem.readW (addr (E s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  have hs := hp.arg_sub hi
  refine (h.frame.readW (Region.contains_self _ _) ?_ (by decide)).trans rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ((hp.sep_pend _ (by simp)).sub_left hs)
  · exact hp.a_o.sub_left hs
  · exact hp.a_s.sub_left hs

/-- `mov d, [esp + 4 + 4i]`: argument `i`. -/
theorem wp_arg {s₀ s : State} (hp : Pre s₀) (h : Common s₀ s) {i : Nat} (hi : i < 7) {d : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (Impl.Rc2.X86.Stream.argOp i)) :: is)) s Q :=
  wp_ldm (b := .esp) (o := 4 + 4 * i) h.esp (hp.rin h.rd hi) fun s' u => k s' (h.arg hp hi ▸ u)

/-- `Common` after writing within the pending block or `out`. -/
theorem Common.write {s₀ s s' : State} (hp : Pre s₀) (h : Common s₀ s) {r : Region}
    (hr : Region.Sub r (pendR s₀) ∨ Region.Sub r (oR s₀)) (f : Frame [r] s.mem s'.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hesp : s'.gpr .esp = s.gpr .esp)
    (hedi : s'.gpr .edi = s.gpr .edi) (hebp : s'.gpr .ebp = s.gpr .ebp) : Common s₀ s' := by
  have sd : ∀ {e : Nat}, e + 4 ≤ 576 → r.Disjoint ⟨addr (scr s₀) e, 4⟩ := fun he => by
    rcases hr with hr | hr
    · exact ((hp.c_s.sub_left Pre.pend_sub).sub_left hr).sub_right (hp.scr_sub he)
    · exact (hp.o_s.sub_left hr).sub_right (hp.scr_sub he)
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hesp.trans h.esp, hedi.trans h.edi, hebp.trans h.ebp,
    h.frame.trans (f.sub ?_), ?_, ?_⟩
  · intro r' hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    rcases hr with hr | hr
    · exact ⟨_, by simp, hr⟩
    · exact ⟨_, by simp, hr⟩
  · rw [f.readW (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact (sd (by decide)).symm) (by decide)]
    exact h.ebx
  · rw [f.readW (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact (sd (by decide)).symm) (by decide)]
    exact h.esi

end VG.Proof.Rc2.X86.Stream.Update

end

/-!
# Streaming RC2-CBC on x86 (32-bit): the copies of the update functions

Saving our caller's registers (`entry_ok`), and the copies: with no complete
block, the data after the pending bytes (`short_ok`); otherwise the pending
bytes and the first `out_len - pending_len` bytes of data to `out` and the
rest to the pending block (`long_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream
open VG.WriteBytes (writeBytes writeBytes_frame)

theorem Common.upd {s₀ s s' : State} (h : Common s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (h₁ : d ≠ .esp) (h₂ : d ≠ .edi) (h₃ : d ≠ .ebp) : Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, (u.other _ (Ne.symm h₁)).trans h.esp,
    (u.other _ (Ne.symm h₂)).trans h.edi, (u.other _ (Ne.symm h₃)).trans h.ebp,
    by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.ebx, by rw [u.mem]; exact h.esi⟩

theorem Common.fupd {s₀ s s' : State} (h : Common s₀ s) (u : Fupd s s') : Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, by rw [u.gpr]; exact h.esp, by rw [u.gpr]; exact h.edi,
    by rw [u.gpr]; exact h.ebp, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.ebx,
    by rw [u.mem]; exact h.esi⟩

theorem frame_writeBytes (m : Mem) (q : Addr) (xs : List Byte) : Frame [⟨q, xs.length⟩] m (writeBytes m q xs) :=
  writeBytes_frame _ _ _ (Region.contains_self _ _)

/-- A copy leaves `Common`, if it writes within the pending block or `out`. -/
theorem Common.copy {s₀ s s' : State} (hp : Pre s₀) (h : Common s₀ s) {S D : BitVec 32} {sd dd n : Nat}
    (c : CopyPost s S D sd dd n s')
    (hr : Region.Sub ⟨addr D dd, n⟩ (pendR s₀) ∨ Region.Sub ⟨addr D dd, n⟩ (oR s₀)) : Common s₀ s' := by
  refine h.write hp hr ?_ c.rd c.wr (c.other _ (by decide) (by decide) (by decide) (by decide))
    (c.other _ (by decide) (by decide) (by decide) (by decide))
    (c.other _ (by decide) (by decide) (by decide) (by decide))
  have := frame_writeBytes s.mem (addr D dd) (Spec.Rc2.bytesAt s.mem (addr S sd) n)
  rwa [bytesAt_len, ← c.mem] at this

theorem copy_bytes {s s' : State} {S D : BitVec 32} {sd dd n : Nat} (c : CopyPost s S D sd dd n s')
    (hn : n < 2 ^ 64) :
    Spec.Rc2.bytesAt s'.mem (addr D dd) n = Spec.Rc2.bytesAt s.mem (addr S sd) n := by
  have h := bytesAt_writeBytes_self s.mem (addr D dd) (Spec.Rc2.bytesAt s.mem (addr S sd) n)
    (by rw [bytesAt_len]; exact hn)
  rwa [bytesAt_len, ← c.mem] at h

theorem copy_frame {s s' : State} {S D : BitVec 32} {sd dd n : Nat} (c : CopyPost s S D sd dd n s') :
    Frame [⟨addr D dd, n⟩] s.mem s'.mem := by
  have := frame_writeBytes s.mem (addr D dd) (Spec.Rc2.bytesAt s.mem (addr S sd) n)
  rwa [bytesAt_len, ← c.mem] at this

/-! ## Saving our caller's registers -/

theorem entry_ok {s₀ : State} (hp : Pre s₀) {Q : State → Prop}
    (hQ : ∀ s, Common s₀ s → Frame [scR s₀] s₀.mem s.mem → s.zf = some (decide (O s₀ = 0)) → Q s) :
    WP isa (.block entry) s₀ Q := by
  simp only [entry, save, List.cons_append, List.nil_append]
  have sc (d : Nat) (hd : d + 4 ≤ 576) : (scR s₀).Contains (addr (scr s₀) d) (32 / 8) := by
    rw [hp.scr_addr hd]; exact Offset.contains_base _ hd (by omega_arith)
  refine wp_ldm (b := .esp) (o := 4 + 4 * 6) rfl (hp.rin rfl (by decide)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_stm e₁ (hp.sin (u₁.wr) (d := 512) (by decide)) fun s₂ u₂ => ?_
  refine wp_stm (by rw [u₂.gpr]; exact e₁) (hp.sin (u₂.wr.trans u₁.wr) (d := 516) (by decide))
    fun s₃ u₃ => ?_
  have m₃ : s₃.mem = (s₀.mem.writeW (addr (scr s₀) 512) (s₀.gpr .ebx)).writeW (addr (scr s₀) 516)
      (s₀.gpr .esi) := by
    rw [u₃.mem, u₂.mem, u₂.gpr, u₁.mem, u₁.other _ (by decide), u₁.other _ (by decide)]
  have f₃ : Frame [scR s₀] s₀.mem s₃.mem := by
    rw [m₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sc 512 (by decide))).writeW
      (List.mem_singleton_self _) _ (sc 516 (by decide))
  have g₃ (r : Reg) (hr : r ≠ .eax) : s₃.gpr r = s₀.gpr r := by
    rw [u₃.gpr, u₂.gpr]; exact u₁.other r hr
  have c₃ : Common s₀ s₃ := by
    refine ⟨by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], g₃ _ (by decide), g₃ _ (by decide),
      g₃ _ (by decide), f₃.mono (by simp), ?_, ?_⟩
    · rw [m₃, Mem.readW_writeW_sep _ (by decide), Mem.readW_writeW_self32]
      rw [hp.scr_addr (d := 512) (by decide), hp.scr_addr (d := 516) (by decide)]
      exact Offset.sep _ (by decide) (by decide) (by decide)
    · rw [m₃, Mem.readW_writeW_self32]
  refine wp_arg hp c₃ (i := 5) (by decide) fun s₄ u₄ => wp_test fun s₅ f₅ hz₅ => WP.block_nil ?_
  refine hQ s₅ ((c₃.upd u₄ (by decide) (by decide) (by decide)).fupd f₅) (by rw [f₅.mem, u₄.mem]; exact f₃) ?_
  rw [hz₅, u₄.gpr, BitVec.and_self, ← ofNat_toNat (arg s₀ 5), ofNat_beq_zero (arg s₀ 5).isLt]

/-! ## No complete block -/

theorem short_ok {s₀ s : State} (hp : Pre s₀) (hO : O s₀ = 0) (hc : Common s₀ s)
    (hf : Frame [scR s₀] s₀.mem s.mem) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' →
      Spec.Rc2.bytesAt s'.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀ + len s₀) =
        Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (dA s₀) (len s₀) → Q s') :
    WP isa short s Q := by
  have hpl : p s₀ + len s₀ < 8 := by have := hp.O_eq; omega_arith
  have hcf := hp.c_fit
  have hdf := hp.d_fit
  rw [short]
  refine WP.seq ?_
  refine wp_arg hp hc (i := 2) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 0) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_arg hp c₂ (i := 1) (by decide) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_add fun s₄ u₄ _ => ?_
  have c₄ := c₃.upd u₄ (by decide) (by decide) (by decide)
  refine wp_arg hp c₄ (i := 3) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  have esi₅ : s₅.gpr .esi = dp s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr]
  have edx₅ : s₅.gpr .edx = ctx s₀ + BitVec.ofNat 32 (p s₀) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₃.gpr, u₂.gpr, ofNat_toNat]
  have ecx₅ : s₅.gpr .ecx = BitVec.ofNat 32 (len s₀) := by rw [u₅.gpr, ofNat_toNat]
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hS : addr (dp s₀) 0 = dA s₀ := by
    rw [addr_eq (by have := (dp s₀).isLt; omega_arith)]; exact BitVec.add_zero _
  have hD : addr (ctx s₀ + BitVec.ofNat 32 (p s₀)) 136 = cA s₀ + BitVec.ofNat 64 (p s₀ + 136) :=
    addr_add (by omega_arith)
  have dst : Region.Sub ⟨cA s₀ + BitVec.ofNat 64 (p s₀ + 136), len s₀⟩ (pendR s₀) :=
    Offset.sub _ (by omega_arith) (by omega_arith)
  refine copy_ok (sd := 0) (dd := 136) (n := len s₀) (S := dp s₀) (D := ctx s₀ + BitVec.ofNat 32 (p s₀))
    (arg s₀ 3).isLt (by omega_arith) (by rw [toNat_add_ofNat (by omega_arith)]; omega_arith)
    (fun i hi => by
      rw [c₅.rd, c₅.wr, hS]
      exact inBytes (R := dR s₀) (by simp [hp.rd]) (fun _ h => h) (by omega_arith) i hi)
    (fun i hi => by
      rw [c₅.wr, hD]
      exact inBytes (R := ctxR s₀) (by simp [hp.wr]) (fun a h => Pre.pend_sub a (dst a h)) (by omega_arith) i hi)
    (by rw [hS, hD]; exact hp.c_d.symm.sub_right (fun a h => Pre.pend_sub a (dst a h)))
    esi₅ edx₅ ecx₅ fun s' c => hQ s' (c₅.copy hp c (.inl (by rw [hD]; exact dst))) ?_
  have hw := bytesAt_writeBytes s.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀)
    (Spec.Rc2.bytesAt s.mem (dA s₀) (len s₀)) (by rw [bytesAt_len]; omega_arith)
  rw [bytesAt_len, Offset.add_add, Nat.add_comm 136] at hw
  rw [c.mem, mem₅, hS, hD, hw,
    Proof.Rc2.bytesAt_frame hf _ _ (by omega_arith) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_s.sub_left (fun a h => Pre.pend_sub a (Offset.sub _ (by omega_arith) (by omega_arith) a h)))),
    Proof.Rc2.bytesAt_frame hf _ _ (by omega_arith) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.d_s)]

end VG.Proof.Rc2.X86.Stream.Update

end

/-!
# Streaming RC2-CBC on x86 (32-bit): the copies before CBC

With `out_len ≠ 0`: the pending bytes and the first `out_len - pending_len`
bytes of data to `out`, and the rest of the data to the pending block
(`long_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

theorem sub_eq' (x y : BitVec 32) (h : y.toNat ≤ x.toNat) : x - y = BitVec.ofNat 32 (x.toNat - y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega_arith

theorem sub_add_eq (x y z : BitVec 32) (h : y.toNat ≤ z.toNat + x.toNat) :
    x - y + z = BitVec.ofNat 32 (z.toNat + x.toNat - y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt; have := y.isLt; have := z.isLt
  omega_arith

section
variable {s₀ s : State} (hp : Pre s₀) (hc : Common s₀ s) {Q : State → Prop}
include hp hc

theorem toOut₁_ok
    (hQ : ∀ t, Common s₀ t → t.mem = s.mem → t.gpr .esi = ctx s₀ → t.gpr .edx = op s₀ →
      t.gpr .ecx = BitVec.ofNat 32 (p s₀) → Q t) :
    WP isa (.block toOut₁) s Q := by
  refine wp_arg hp hc (i := 0) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 4) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_arg hp c₂ (i := 1) (by decide) fun s₃ u₃ => WP.block_nil ?_
  exact hQ s₃ (c₂.upd u₃ (by decide) (by decide) (by decide)) (by rw [u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₃.other _ (by decide), u₂.gpr]) (by rw [u₃.gpr, ofNat_toNat])

theorem toOut₂_ok (hpO : p s₀ ≤ O s₀)
    (hQ : ∀ t, Common s₀ t → t.mem = s.mem → t.gpr .esi = dp s₀ → t.gpr .edx = s.gpr .edx →
      t.gpr .ecx = BitVec.ofNat 32 (O s₀ - p s₀) → Q t) :
    WP isa (.block toOut₂) s Q := by
  refine wp_arg hp hc (i := 2) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 5) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_arg hp c₂ (i := 1) (by decide) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_sub fun s₄ u₄ _ => WP.block_nil ?_
  refine hQ s₄ (c₃.upd u₄ (by decide) (by decide) (by decide)) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]) ?_
  rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr]
  exact sub_eq' _ _ hpO

theorem toPending_ok (hle : O s₀ ≤ p s₀ + len s₀)
    (hQ : ∀ t, Common s₀ t → t.mem = s.mem → t.gpr .esi = s.gpr .esi → t.gpr .edx = ctx s₀ →
      t.gpr .ecx = BitVec.ofNat 32 (p s₀ + len s₀ - O s₀) → Q t) :
    WP isa (.block toPending) s Q := by
  refine wp_arg hp hc (i := 0) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 3) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_arg hp c₂ (i := 5) (by decide) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_sub fun s₄ u₄ _ => ?_
  have c₄ := c₃.upd u₄ (by decide) (by decide) (by decide)
  refine wp_arg hp c₄ (i := 1) (by decide) fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine wp_add fun s₆ u₆ _ => WP.block_nil ?_
  refine hQ s₆ (c₅.upd u₆ (by decide) (by decide) (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]) ?_
  rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr]
  exact sub_add_eq _ _ _ hle

end

theorem long_ok {s₀ s : State} (hp : Pre s₀) (hO : O s₀ ≠ 0) (hc : Common s₀ s)
    (hf : Frame [scR s₀] s₀.mem s.mem) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' →
      Spec.Rc2.bytesAt s'.mem (oA s₀) (O s₀) =
        Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (dA s₀) (O s₀ - p s₀) →
      Spec.Rc2.bytesAt s'.mem (cA s₀ + BitVec.ofNat 64 136) ((p s₀ + len s₀) % 8) =
        Spec.Rc2.bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 (O s₀ - p s₀)) ((p s₀ + len s₀) % 8) → Q s') :
    WP isa long s Q := by
  have hOe := hp.O_eq
  have hpl := hp.p_lt
  have hpO : p s₀ ≤ O s₀ := by omega_arith
  have hOL : O s₀ - p s₀ ≤ len s₀ := by omega_arith
  have hR : p s₀ + len s₀ - O s₀ = (p s₀ + len s₀) % 8 := by omega_arith
  have hRlt : (p s₀ + len s₀) % 8 < 8 := Nat.mod_lt _ (by decide)
  have hcf := hp.c_fit
  have hdf := hp.d_fit
  have hof := hp.o_fit
  have hlen : len s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have hOlt : O s₀ < 2 ^ 32 := (arg s₀ 5).isLt
  have hC : addr (ctx s₀) 136 = cA s₀ + BitVec.ofNat 64 136 := addr_eq (by omega_arith)
  have hS : addr (dp s₀) 0 = dA s₀ := by
    rw [addr_eq (by have := (dp s₀).isLt; omega_arith)]; exact BitVec.add_zero _
  have hO0 : addr (op s₀) 0 = oA s₀ := by
    rw [addr_eq (by have := (op s₀).isLt; omega_arith)]; exact BitVec.add_zero _
  have hOp : addr (op s₀ + BitVec.ofNat 32 (p s₀)) 0 = oA s₀ + BitVec.ofNat 64 (p s₀) := by
    rw [addr_add (by omega_arith), Nat.add_zero]
  have hSp (h0 : 0 < (p s₀ + len s₀) % 8) :
      addr (dp s₀ + BitVec.ofNat 32 (O s₀ - p s₀)) 0 = dA s₀ + BitVec.ofNat 64 (O s₀ - p s₀) := by
    rw [addr_add (by omega_arith), Nat.add_zero]
  have inR {a : Addr} {n : Nat} {R : Region} (hR : R ∈ s₀.rd ++ s₀.wr) (hs : Region.Sub ⟨a, n⟩ R)
      (hn : n < 2 ^ 64) {t : State} (hc : Common s₀ t) :
      ∀ i < n, InRegions (t.rd ++ t.wr) (a + BitVec.ofNat 64 i) 1 := by
    rw [hc.rd, hc.wr]; exact inBytes hR hs hn
  have outR {a : Addr} {n : Nat} {R : Region} (hR : R ∈ s₀.wr) (hs : Region.Sub ⟨a, n⟩ R)
      (hn : n < 2 ^ 64) {t : State} (hc : Common s₀ t) : ∀ i < n, InRegions t.wr (a + BitVec.ofNat 64 i) 1 := by
    rw [hc.wr]; exact inBytes hR hs hn
  have ctxIn : ctxR s₀ ∈ s₀.wr := by simp [hp.wr]
  have oIn : oR s₀ ∈ s₀.wr := by simp [hp.wr]
  have ctxIn' : ctxR s₀ ∈ s₀.rd ++ s₀.wr := List.mem_append_right _ ctxIn
  have dIn : dR s₀ ∈ s₀.rd ++ s₀.wr := List.mem_append_left _ (by simp [hp.rd])
  have pendSrc : Region.Sub ⟨cA s₀ + BitVec.ofNat 64 136, p s₀⟩ (pendR s₀) := Region.sub_prefix (by omega_arith)
  have pendDst : Region.Sub ⟨cA s₀ + BitVec.ofNat 64 136, (p s₀ + len s₀) % 8⟩ (pendR s₀) :=
    Region.sub_prefix (by omega_arith)
  have outA : Region.Sub ⟨oA s₀, p s₀⟩ (oR s₀) := Region.sub_prefix hpO
  have outB : Region.Sub ⟨oA s₀ + BitVec.ofNat 64 (p s₀), O s₀ - p s₀⟩ (oR s₀) :=
    Offset.sub_base _ (by omega_arith)
  have datA : Region.Sub ⟨dA s₀, O s₀ - p s₀⟩ (dR s₀) := Region.sub_prefix hOL
  have datB : Region.Sub ⟨dA s₀ + BitVec.ofNat 64 (O s₀ - p s₀), (p s₀ + len s₀) % 8⟩ (dR s₀) :=
    Offset.sub_base _ (by omega_arith)
  have pc {r : Region} (h : Region.Sub r (pendR s₀)) : Region.Sub r (ctxR s₀) :=
    fun a ha => Pre.pend_sub a (h a ha)
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  -- The pending bytes to `out`.
  refine WP.seq (toOut₁_ok hp hc fun s₁ c₁ mem₁ esi₁ edx₁ ecx₁ => ?_)
  refine WP.seq (copy_ok (sd := 136) (dd := 0) (n := p s₀) (S := ctx s₀) (D := op s₀) (by omega_arith)
    (by omega_arith) (by omega_arith)
    (by rw [hC]; exact inR ctxIn' (pc pendSrc) (by omega_arith) c₁)
    (by rw [hO0]; exact outR oIn outA (by omega_arith) c₁)
    (by rw [hC, hO0]; exact (hp.c_o.sub_left (pc pendSrc)).sub_right outA)
    esi₁ edx₁ ecx₁ fun s₂ k₂ => ?_)
  have c₂ := c₁.copy hp k₂ (.inr (by rw [hO0]; exact outA))
  have f₂ := copy_frame k₂
  have b₂ := copy_bytes k₂ (by omega_arith)
  rw [hO0] at f₂ b₂
  rw [hC, mem₁] at b₂
  -- The first `out_len - pending_len` bytes of data after them.
  refine WP.seq (toOut₂_ok hp c₂ hpO fun s₃ c₃ mem₃ esi₃ edx₃ ecx₃ => ?_)
  rw [k₂.edx] at edx₃
  refine WP.seq (copy_ok (sd := 0) (dd := 0) (n := O s₀ - p s₀) (S := dp s₀)
    (D := op s₀ + BitVec.ofNat 32 (p s₀)) (by omega_arith) (by omega_arith)
    (by rw [toNat_add_ofNat (by omega_arith)]; omega_arith)
    (by rw [hS]; exact inR dIn datA (by omega_arith) c₃)
    (by rw [hOp]; exact outR oIn outB (by omega_arith) c₃)
    (by rw [hS, hOp]; exact (hp.d_o.sub_left datA).sub_right outB)
    esi₃ edx₃ ecx₃ fun s₄ k₄ => ?_)
  have c₄ := c₃.copy hp k₄ (.inr (by rw [hOp]; exact outB))
  have f₄ := copy_frame k₄
  have b₄ := copy_bytes k₄ (by omega_arith)
  rw [hOp] at f₄ b₄
  rw [hS, mem₃] at b₄
  -- The rest to the pending block.
  refine WP.seq (toPending_ok hp c₄ (by omega_arith) fun s₅ c₅ mem₅ esi₅ edx₅ ecx₅ => ?_)
  rw [k₄.esi] at esi₅
  rw [hR] at ecx₅
  refine copy_ok (sd := 0) (dd := 136) (n := (p s₀ + len s₀) % 8)
    (S := dp s₀ + BitVec.ofNat 32 (O s₀ - p s₀)) (D := ctx s₀) (by omega_arith)
    (by
      rcases Nat.eq_zero_or_pos ((p s₀ + len s₀) % 8) with h0 | h0
      · have := (dp s₀ + BitVec.ofNat 32 (O s₀ - p s₀)).isLt; omega_arith
      · rw [toNat_add_ofNat (by omega_arith)]; omega_arith) (by omega_arith)
    (fun i hi => by rw [hSp (by omega_arith)]; exact inR dIn datB (by omega_arith) c₅ i hi)
    (by rw [hC]; exact outR ctxIn (pc pendDst) (by omega_arith) c₅)
    (by
      rcases Nat.eq_zero_or_pos ((p s₀ + len s₀) % 8) with h0 | h0
      · intro a h; simp only [Region.Contains, h0] at h; omega_arith
      · rw [hSp h0, hC]; exact (hp.c_d.symm.sub_left datB).sub_right (pc pendDst))
    esi₅ edx₅ ecx₅ fun s₆ k₆ => ?_
  have c₆ := c₅.copy hp k₆ (.inl (by rw [hC]; exact pendDst))
  have f₆ := copy_frame k₆
  have b₆ := copy_bytes k₆ (by omega_arith)
  rw [hC] at f₆ b₆
  rw [mem₅] at b₆
  rw [mem₅] at f₆
  rw [mem₃] at f₄
  rw [mem₁] at f₂
  refine hQ s₆ c₆ ?_ ?_
  · -- `out`: the pending bytes, then the data.
    have hsplit : Spec.Rc2.bytesAt s₆.mem (oA s₀) (O s₀) = Spec.Rc2.bytesAt s₆.mem (oA s₀) (p s₀) ++
        Spec.Rc2.bytesAt s₆.mem (oA s₀ + BitVec.ofNat 64 (p s₀)) (O s₀ - p s₀) := by
      rw [← Proof.Rc2.bytesAt_add, Nat.add_sub_cancel' hpO]
    have e₁ : Spec.Rc2.bytesAt s₆.mem (oA s₀) (p s₀) =
        Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) := by
      rw [Proof.Rc2.bytesAt_frame f₆ _ _ (by omega_arith) (sing ((hp.c_o.sub_left (pc pendDst)).sub_right outA).symm),
        Proof.Rc2.bytesAt_frame f₄ _ _ (by omega_arith) (sing (Offset.base_disjoint _ (by omega_arith) (by omega_arith))), b₂,
        Proof.Rc2.bytesAt_frame hf _ _ (by omega_arith) (sing (hp.c_s.sub_left (pc pendSrc)))]
    have e₂ : Spec.Rc2.bytesAt s₆.mem (oA s₀ + BitVec.ofNat 64 (p s₀)) (O s₀ - p s₀) =
        Spec.Rc2.bytesAt s₀.mem (dA s₀) (O s₀ - p s₀) := by
      rw [Proof.Rc2.bytesAt_frame f₆ _ _ (by omega_arith) (sing ((hp.c_o.sub_left (pc pendDst)).sub_right outB).symm),
        b₄, Proof.Rc2.bytesAt_frame f₂ _ _ (by omega_arith) (sing ((hp.d_o.sub_left datA).sub_right outA)),
        Proof.Rc2.bytesAt_frame hf _ _ (by omega_arith) (sing (hp.d_s.sub_left datA))]
    rw [hsplit, e₁, e₂]
  · -- The pending block: the rest of the data.
    rcases Nat.eq_zero_or_pos ((p s₀ + len s₀) % 8) with h0 | h0
    · rw [h0]; rfl
    rw [b₆, hSp h0, Proof.Rc2.bytesAt_frame f₄ _ _ (by omega_arith) (sing ((hp.d_o.sub_left datB).sub_right outB)),
      Proof.Rc2.bytesAt_frame f₂ _ _ (by omega_arith) (sing ((hp.d_o.sub_left datB).sub_right outA)),
      Proof.Rc2.bytesAt_frame hf _ _ (by omega_arith) (sing (hp.d_s.sub_left datB))]

end VG.Proof.Rc2.X86.Stream.Update
