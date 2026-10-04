import VerifiedGarbage.Proof.Rc2.X86.KeyCorrect
import VerifiedGarbage.Proof.Rc2.X86.KeyLit
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Rc2.X86.Stream.Contract
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rc2.CbcMemory

section

/-!
# Streaming RC2-CBC on x86 (32-bit): `init` before the call

Names for the arguments and regions of `init` (`Pre`), the length checks
(`checks_ok`), and the copy of the IV and the arguments of the key expansion
(`initArgs_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

theorem ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev key : BitVec 32 := arg s₀ 0
abbrev kl : Nat := (arg s₀ 1).toNat
abbrev eb : Nat := (arg s₀ 2).toNat
abbrev iv : BitVec 32 := arg s₀ 3
abbrev il : Nat := (arg s₀ 4).toNat
abbrev ctx : BitVec 32 := arg s₀ 5
abbrev scr : BitVec 32 := arg s₀ 6
abbrev kA : Addr := (key s₀).setWidth 64
abbrev ivA : Addr := (iv s₀).setWidth 64
abbrev cA : Addr := (ctx s₀).setWidth 64
abbrev sA : Addr := (scr s₀).setWidth 64
abbrev keyR : Region := ⟨kA s₀, kl s₀⟩
abbrev ivR : Region := ⟨ivA s₀, il s₀⟩
abbrev ctxR : Region := ⟨cA s₀, 144⟩
abbrev scR : Region := ⟨sA s₀, 576⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 24
/-- Where the chaining value goes. -/
abbrev cvR : Region := ⟨cA s₀ + BitVec.ofNat 64 128, 8⟩
abbrev schR : Region := ⟨cA s₀, 128⟩

/-- The value `init` returns. -/
def code : Nat :=
  if ¬(1 ≤ kl s₀ ∧ kl s₀ ≤ 128) then 1 else if ¬(1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) then 2
  else if il s₀ ≠ 8 then 3 else 0

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, ivR s₀, argR s₀]
  wr : s₀.wr = [ctxR s₀, scR s₀]
  k_c : (keyR s₀).Disjoint (ctxR s₀)
  k_s : (keyR s₀).Disjoint (scR s₀)
  i_c : (ivR s₀).Disjoint (ctxR s₀)
  i_s : (ivR s₀).Disjoint (scR s₀)
  c_s : (ctxR s₀).Disjoint (scR s₀)
  a_c : (argR s₀).Disjoint (ctxR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  r_c : (retR s₀).Disjoint (ctxR s₀)
  r_s : (retR s₀).Disjoint (scR s₀)
  t_k : (stkR s₀).Disjoint (keyR s₀)
  t_i : (stkR s₀).Disjoint (ivR s₀)
  t_c : (stkR s₀).Disjoint (ctxR s₀)
  t_s : (stkR s₀).Disjoint (scR s₀)
  k_fit : (key s₀).toNat + kl s₀ ≤ 2 ^ 32
  i_fit : (iv s₀).toNat + il s₀ ≤ 2 ^ 32
  c_fit : (ctx s₀).toNat + 144 ≤ 2 ^ 32
  s_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 24 ≤ (E s₀).toNat
  sp_fit : (E s₀).toNat + 32 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : initContract.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

theorem cv_sub {s₀ : State} : Region.Sub (cvR s₀) (ctxR s₀) := Offset.sub_base _ (by decide)
theorem sch_sub {s₀ : State} : Region.Sub (schR s₀) (ctxR s₀) := Region.sub_prefix (by decide)
theorem sch_cv {s₀ : State} : (schR s₀).Disjoint (cvR s₀) := Offset.base_disjoint _ (by decide) (by decide)

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem argAddr_eq (i : Nat) (hi : i < 7) :
    addr (E s₀) (4 + 4 * i) = (E s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
  have := hp.sp_fit; exact addr_eq (by omega)

theorem arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨addr (E s₀) (4 + 4 * i), 4⟩ (argR s₀) := by
  show Region.Sub _ ⟨addr (E s₀) (4 + 4 * 0), 28⟩
  rw [hp.argAddr_eq i hi, hp.argAddr_eq 0 (by decide)]
  exact Offset.sub _ (by omega) (by omega)

theorem rin {s : State} (hrd : s.rd = s₀.rd) {i : Nat} (hi : i < 7) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [hrd, hp.rd], ?_⟩
  show (⟨addr (E s₀) (4 + 4 * 0), 28⟩ : Region).Contains _ _
  rw [hp.argAddr_eq i hi, hp.argAddr_eq 0 (by decide)]
  exact Offset.contains _ (by omega) (by omega) (by have := hp.sp_fit; omega)

theorem scr_addr {d : Nat} (hd : d + 4 ≤ 576) : addr (scr s₀) d = sA s₀ + BitVec.ofNat 64 d := by
  have := hp.s_fit; exact addr_eq (by omega)

theorem scr_sub {d : Nat} (hd : d + 4 ≤ 576) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [hp.scr_addr hd]; exact Offset.sub_base _ hd

theorem ctx_addr {d : Nat} (hd : d + 4 ≤ 144) : addr (ctx s₀) d = cA s₀ + BitVec.ofNat 64 d := by
  have := hp.c_fit; exact addr_eq (by omega)

end Pre

/-- What holds before the call. -/
structure Common (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  edi : s.gpr .edi = s₀.gpr .edi
  ebp : s.gpr .ebp = s₀.gpr .ebp
  frame : Frame [cvR s₀, scR s₀] s₀.mem s.mem

theorem Common.refl (s₀ : State) : Common s₀ s₀ := ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Common.upd {s₀ s s' : State} (h : Common s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (h₁ : d ≠ .esp) (h₂ : d ≠ .edi) (h₃ : d ≠ .ebp) : Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, (u.other _ (Ne.symm h₁)).trans h.esp,
    (u.other _ (Ne.symm h₂)).trans h.edi, (u.other _ (Ne.symm h₃)).trans h.ebp,
    by rw [u.mem]; exact h.frame⟩

theorem Common.fupd {s₀ s s' : State} (h : Common s₀ s) (u : Fupd s s') : Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, by rw [u.gpr]; exact h.esp, by rw [u.gpr]; exact h.edi,
    by rw [u.gpr]; exact h.ebp, by rw [u.mem]; exact h.frame⟩

theorem Common.arg {s₀ s : State} (hp : Pre s₀) (h : Common s₀ s) {i : Nat} (hi : i < 7) :
    s.mem.readW (addr (E s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  have hs := hp.arg_sub hi
  refine (h.frame.readW (Region.contains_self _ _) ?_ (by decide)).trans rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hp.a_c.sub_right cv_sub).sub_left hs
  · exact hp.a_s.sub_left hs

theorem wp_arg {s₀ s : State} (hp : Pre s₀) (h : Common s₀ s) {i : Nat} (hi : i < 7) {d : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (Impl.Rc2.X86.Stream.argOp i)) :: is)) s Q :=
  wp_ldm (b := .esp) (o := 4 + 4 * i) h.esp (hp.rin h.rd hi) fun s' u => k s' (h.arg hp hi ▸ u)

/-! ## The checks -/

theorem pred_lt (x : BitVec 32) {n : Nat} (hn : n < 2 ^ 32) :
    decide ((x - BitVec.ofNat 32 1).toNat < n) = decide (1 ≤ x.toNat ∧ x.toNat ≤ n) := by
  rw [decide_eq_decide, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem checks_ok {s₀ : State} (hp : Pre s₀) {Q : State → Prop}
    (hQ : ∀ t, Common s₀ t → t.mem = s₀.mem → t.gpr .eax = BitVec.ofNat 32 (code s₀) →
      t.gpr .ebx = s₀.gpr .ebx → t.gpr .esi = s₀.gpr .esi → Q t) :
    WP isa checks s₀ Q := by
  have c₀ := Common.refl s₀
  rw [checks]
  refine WP.seq ?_
  refine wp_movi fun s₁ u₁ => ?_
  have c₁ := c₀.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 1) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_subi fun s₃ u₃ _ _ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_cmpi fun s₄ f₄ cf₄ _ => WP.block_nil ?_
  have c₄ := c₃.fupd f₄
  have k₄ : decide (1 ≤ kl s₀ ∧ kl s₀ ≤ 128) = decide ((s₃.gpr .ecx).toNat < (128 : BitVec 32).toNat) := by
    rw [u₃.gpr, u₂.gpr]; exact (pred_lt _ (by decide)).symm
  have m₄ : s₄.mem = s₀.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g₄ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) : s₄.gpr r = s₀.gpr r := by
    rw [f₄.gpr, u₃.other _ h₂, u₂.other _ h₂, u₁.other _ h₁]
  have a₄ : s₄.gpr .eax = BitVec.ofNat 32 1 := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  refine WP.ite (!decide (1 ≤ kl s₀ ∧ kl s₀ ≤ 128)) (by
    show s₄.cf.map (!·) = _; rw [cf₄, ← k₄]; rfl) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hk : ¬(1 ≤ kl s₀ ∧ kl s₀ ≤ 128) := of_decide_eq_false (by revert hb; cases decide (1 ≤ kl s₀ ∧ kl s₀ ≤ 128) <;> simp)
    refine hQ s₄ c₄ m₄ (by rw [a₄, code, ite_eq_left_of_eq_true _ _ (eq_true hk)]) (g₄ _ (by decide) (by decide))
      (g₄ _ (by decide) (by decide))
  have hk : 1 ≤ kl s₀ ∧ kl s₀ ≤ 128 := of_decide_eq_true (by revert hb; cases decide (1 ≤ kl s₀ ∧ kl s₀ ≤ 128) <;> simp)
  -- `effective_bits`.
  refine WP.seq ?_
  refine wp_movi fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine wp_arg hp c₅ (i := 2) (by decide) fun s₆ u₆ => ?_
  have c₆ := c₅.upd u₆ (by decide) (by decide) (by decide)
  refine wp_subi fun s₇ u₇ _ _ => ?_
  have c₇ := c₆.upd u₇ (by decide) (by decide) (by decide)
  refine wp_cmpi fun s₈ f₈ cf₈ _ => WP.block_nil ?_
  have c₈ := c₇.fupd f₈
  have k₈ : decide (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) = decide ((s₇.gpr .ecx).toNat < (1024 : BitVec 32).toNat) := by
    rw [u₇.gpr, u₆.gpr]; exact (pred_lt _ (by decide)).symm
  have m₈ : s₈.mem = s₀.mem := by rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
  have g₈ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) : s₈.gpr r = s₀.gpr r := by
    rw [f₈.gpr, u₇.other _ h₂, u₆.other _ h₂, u₅.other _ h₁, g₄ _ h₁ h₂]
  have a₈ : s₈.gpr .eax = BitVec.ofNat 32 2 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  refine WP.ite (!decide (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024)) (by
    show s₈.cf.map (!·) = _; rw [cf₈, ← k₈]; rfl) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have he : ¬(1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) := of_decide_eq_false (by revert hb; cases decide (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) <;> simp)
    refine hQ s₈ c₈ m₈ (by rw [a₈, code, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hk)), ite_eq_left_of_eq_true _ _ (eq_true he)]) (g₈ _ (by decide) (by decide)) (g₈ _ (by decide) (by decide))
  have he : 1 ≤ eb s₀ ∧ eb s₀ ≤ 1024 := of_decide_eq_true (by revert hb; cases decide (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) <;> simp)
  -- `iv_len`.
  refine WP.seq ?_
  refine wp_movi fun s₉ u₉ => ?_
  have c₉ := c₈.upd u₉ (by decide) (by decide) (by decide)
  refine wp_arg hp c₉ (i := 4) (by decide) fun s₁₀ u₁₀ => ?_
  have c₁₀ := c₉.upd u₁₀ (by decide) (by decide) (by decide)
  refine wp_cmpi fun s₁₁ f₁₁ _ zf₁₁ => WP.block_nil ?_
  have c₁₁ := c₁₀.fupd f₁₁
  have m₁₁ : s₁₁.mem = s₀.mem := by rw [f₁₁.mem, u₁₀.mem, u₉.mem, m₈]
  have g₁₁ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) : s₁₁.gpr r = s₀.gpr r := by
    rw [f₁₁.gpr, u₁₀.other _ h₂, u₉.other _ h₁, g₈ _ h₁ h₂]
  have z : (s₁₀.gpr .ecx - 8 == 0) = decide (il s₀ = 8) := by
    rw [u₁₀.gpr, ← ofNat_toNat (arg s₀ 4)]
    exact sub_beq (arg s₀ 4).isLt (by decide)
  refine WP.ite (!decide (il s₀ = 8)) (by
    show s₁₁.zf.map (!·) = _; rw [zf₁₁, z]; rfl) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hi : il s₀ ≠ 8 := of_decide_eq_false (by revert hb; cases decide (il s₀ = 8) <;> simp)
    refine hQ s₁₁ c₁₁ m₁₁ ?_ (g₁₁ _ (by decide) (by decide)) (g₁₁ _ (by decide) (by decide))
    rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr]
    rw [code, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hk)), ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro he)), ite_eq_left_of_eq_true _ _ (eq_true hi)]
  · have hi : il s₀ = 8 := of_decide_eq_true (by revert hb; cases decide (il s₀ = 8) <;> simp)
    refine wp_movi fun s₁₂ u₁₂ => WP.block_nil ?_
    refine hQ s₁₂ (c₁₁.upd u₁₂ (by decide) (by decide) (by decide)) (by rw [u₁₂.mem, m₁₁]) ?_
      (by rw [u₁₂.other _ (by decide)]; exact g₁₁ _ (by decide) (by decide))
      (by rw [u₁₂.other _ (by decide)]; exact g₁₁ _ (by decide) (by decide))
    rw [u₁₂.gpr]
    rw [code, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hk)), ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro he)), ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hi))]

end VG.Proof.Rc2.X86.Stream.Init

end

section

/-!
# Streaming RC2-CBC on x86 (32-bit): the IV and the key expansion's arguments

With valid lengths, `init` copies the IV to `ctx + 128`, saves our caller's
`ebx` and `esi` in `scratch[512..520)`, and loads the arguments of
`vg_rc2_expand_key` (`initArgs_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

/-- `Common` after a store within the chaining value or the scratch space. -/
theorem Common.store {s₀ s s' : State} (h : Common s₀ s) {a : Addr} {v : BitVec 32}
    (u : Mupd s s' (s.mem.writeW a v)) {r : Region} (hr : r ∈ [cvR s₀, scR s₀]) (ha : r.Contains a 4) :
    Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, by rw [u.gpr]; exact h.esp, by rw [u.gpr]; exact h.edi,
    by rw [u.gpr]; exact h.ebp, by rw [u.mem]; exact h.frame.writeW hr _ ha⟩

theorem initArgs_ok {s₀ s : State} (hp : Pre s₀) (hi : il s₀ = 8) (hc : Common s₀ s) (hm : s.mem = s₀.mem)
    (hb : s.gpr .ebx = s₀.gpr .ebx) (hs : s.gpr .esi = s₀.gpr .esi) {Q : State → Prop}
    (hQ : ∀ t, Common s₀ t → t.gpr .eax = key s₀ → t.gpr .ecx = arg s₀ 1 → t.gpr .edx = arg s₀ 2 →
      t.gpr .esi = ctx s₀ → t.gpr .ebx = scr s₀ →
      Spec.Rc2.blockAt t.mem (cA s₀ + BitVec.ofNat 64 128) = Spec.Rc2.blockAt s₀.mem (ivA s₀) →
      t.mem.readW (addr (scr s₀) 512) 32 = s₀.gpr .ebx → t.mem.readW (addr (scr s₀) 516) 32 = s₀.gpr .esi →
      Q t) :
    WP isa (.block initArgs) s Q := by
  have hif := hp.i_fit
  have hcf := hp.c_fit
  have iv4 : addr (iv s₀) 4 = ivA s₀ + BitVec.ofNat 64 4 := addr_eq (by omega)
  have c128 : addr (ctx s₀) 128 = cA s₀ + BitVec.ofNat 64 128 := hp.ctx_addr (by decide)
  have c132 : addr (ctx s₀) 132 = cA s₀ + BitVec.ofNat 64 132 := hp.ctx_addr (by decide)
  have ivIn₀ : InRegions (s₀.rd ++ s₀.wr) (addr (iv s₀) 0) 4 := by
    rw [addr_eq (by have := (iv s₀).isLt; omega)]
    exact ⟨ivR s₀, by simp [hp.rd], Offset.contains_base _ (by omega) (by omega)⟩
  have ivIn₄ : InRegions (s₀.rd ++ s₀.wr) (addr (iv s₀) 4) 4 := by
    rw [iv4]; exact ⟨ivR s₀, by simp [hp.rd], Offset.contains_base _ (by omega) (by omega)⟩
  have iv0 : addr (iv s₀) 0 = ivA s₀ := by
    rw [addr_eq (by have := (iv s₀).isLt; omega)]; exact BitVec.add_zero _
  have cvC (d : Nat) (hd : 128 ≤ d) (hd' : d + 4 ≤ 136) : (cvR s₀).Contains (cA s₀ + BitVec.ofNat 64 d) 4 :=
    Offset.contains _ hd (by omega) (by omega)
  have cvIn (d : Nat) (hd : 128 ≤ d) (hd' : d + 4 ≤ 136) : InRegions s₀.wr (cA s₀ + BitVec.ofNat 64 d) 4 :=
    ⟨ctxR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  have scC (d : Nat) (hd : d + 4 ≤ 576) : (scR s₀).Contains (addr (scr s₀) d) 4 := by
    rw [hp.scr_addr hd]; exact Offset.contains_base _ hd (by omega)
  have scIn (d : Nat) (hd : d + 4 ≤ 576) : InRegions s₀.wr (addr (scr s₀) d) 4 :=
    ⟨scR s₀, by simp [hp.wr], scC d hd⟩
  simp only [initArgs, save, List.cons_append, List.nil_append]
  refine wp_arg hp hc (i := 3) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 5) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  have eax₂ : s₂.gpr .eax = iv s₀ := by rw [u₂.other _ (by decide)]; exact u₁.gpr
  refine wp_ldm (o := 0) eax₂ (by rw [c₂.rd, c₂.wr]; exact ivIn₀) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_stm (o := 128) (B := ctx s₀) (by rw [u₃.other _ (by decide)]; exact u₂.gpr)
    (by rw [u₃.wr, c₂.wr, c128]; exact cvIn 128 (by decide) (by decide)) fun s₄ u₄ => ?_
  have c₄ := c₃.store u₄ (r := cvR s₀) (by simp) (by rw [c128]; exact cvC 128 (by decide) (by decide))
  refine wp_ldm (o := 4) (B := iv s₀) (by rw [u₄.gpr, u₃.other _ (by decide)]; exact eax₂)
    (by rw [c₄.rd, c₄.wr]; exact ivIn₄) fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine wp_stm (o := 132) (B := ctx s₀) (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact u₂.gpr)
    (by rw [u₅.wr, c₄.wr, c132]; exact cvIn 132 (by decide) (by decide)) fun s₆ u₆ => ?_
  have c₆ := c₅.store u₆ (r := cvR s₀) (by simp) (by rw [c132]; exact cvC 132 (by decide) (by decide))
  -- The chaining value.
  have m₆ : s₆.mem = s₀.mem.writeW (cA s₀ + BitVec.ofNat 64 128) (s₀.mem.readW (ivA s₀) 64) := by
    have r₄ : s₄.mem.readW (ivA s₀ + BitVec.ofNat 64 4) 32 = s₀.mem.readW (ivA s₀ + BitVec.ofNat 64 4) 32 := by
      rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, hm, c128]
      refine Mem.readW_writeW_sep (Region.Disjoint.sep (hp.i_c.sub_right cv_sub) ?_ ?_) (by decide)
      · exact Offset.contains_base _ (by omega) (by omega)
      · exact contains_prefix _ (by decide)
    have m₄ : s₄.mem = s₀.mem.writeW (cA s₀ + BitVec.ofNat 64 128) (s₀.mem.readW (ivA s₀) 32) := by
      rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, hm, iv0, c128]
    rw [u₆.mem, u₅.gpr, u₅.mem, iv4, r₄, c132, m₄,
      show cA s₀ + BitVec.ofNat 64 132 = cA s₀ + BitVec.ofNat 64 128 + BitVec.ofNat 64 4 by
        rw [Offset.add_add],
      ← Word32.write64_pair, ← Word32.read64_pair]
  have cv₆ : Spec.Rc2.blockAt s₆.mem (cA s₀ + BitVec.ofNat 64 128) = Spec.Rc2.blockAt s₀.mem (ivA s₀) := by
    rw [m₆, blockAt_copy]
  -- Our caller's registers.
  refine wp_arg hp c₆ (i := 6) (by decide) fun s₇ u₇ => ?_
  have c₇ := c₆.upd u₇ (by decide) (by decide) (by decide)
  have g₇ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) (h₃ : r ≠ .edx) : s₇.gpr r = s.gpr r := by
    rw [u₇.other _ h₁, u₆.gpr, u₅.other _ h₃, u₄.gpr, u₃.other _ h₃, u₂.other _ h₂, u₁.other _ h₁]
  refine wp_stm (o := 512) (B := scr s₀) u₇.gpr (by rw [u₇.wr, c₆.wr]; exact scIn 512 (by decide)) fun s₈ u₈ => ?_
  have c₈ := c₇.store u₈ (r := scR s₀) (by simp) (scC 512 (by decide))
  refine wp_stm (o := 516) (B := scr s₀) (by rw [u₈.gpr]; exact u₇.gpr) (by rw [u₈.wr, c₇.wr]; exact scIn 516 (by decide))
    fun s₉ u₉ => ?_
  have c₉ := c₈.store u₉ (r := scR s₀) (by simp) (scC 516 (by decide))
  have m₉ : s₉.mem = (s₇.mem.writeW (addr (scr s₀) 512) (s₀.gpr .ebx)).writeW (addr (scr s₀) 516)
      (s₀.gpr .esi) := by
    rw [u₉.mem, u₈.mem, u₈.gpr, g₇ _ (by decide) (by decide) (by decide),
      g₇ _ (by decide) (by decide) (by decide), hb, hs]
  have f₉ : Frame [scR s₀] s₇.mem s₉.mem := by
    rw [m₉]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (scC 512 (by decide))).writeW
      (List.mem_singleton_self _) _ (scC 516 (by decide))
  have cv₉ : Spec.Rc2.blockAt s₉.mem (cA s₀ + BitVec.ofNat 64 128) = Spec.Rc2.blockAt s₀.mem (ivA s₀) := by
    rw [Proof.Rc2.blockAt_frame f₉ _ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.c_s.sub_left cv_sub), u₇.mem]
    exact cv₆
  have w₁ : s₉.mem.readW (addr (scr s₀) 512) 32 = s₀.gpr .ebx := by
    rw [m₉, Mem.readW_writeW_sep _ (by decide), Mem.readW_writeW_self32]
    rw [hp.scr_addr (d := 512) (by decide), hp.scr_addr (d := 516) (by decide)]
    exact Offset.sep _ (by decide) (by decide) (by decide)
  have w₂ : s₉.mem.readW (addr (scr s₀) 516) 32 = s₀.gpr .esi := by rw [m₉, Mem.readW_writeW_self32]
  -- The arguments.
  refine wp_mov fun s₁₀ u₁₀ => ?_
  have c₁₀ := c₉.upd u₁₀ (by decide) (by decide) (by decide)
  refine wp_mov fun s₁₁ u₁₁ => ?_
  have c₁₁ := c₁₀.upd u₁₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁₁ (i := 2) (by decide) fun s₁₂ u₁₂ => ?_
  have c₁₂ := c₁₁.upd u₁₂ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁₂ (i := 1) (by decide) fun s₁₃ u₁₃ => ?_
  have c₁₃ := c₁₂.upd u₁₃ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁₃ (i := 0) (by decide) fun s₁₄ u₁₄ => WP.block_nil ?_
  have mem : s₁₄.mem = s₉.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem]
  refine hQ s₁₄ (c₁₃.upd u₁₄ (by decide) (by decide) (by decide)) u₁₄.gpr
    (by rw [u₁₄.other _ (by decide), u₁₃.gpr])
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr])
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact u₂.gpr)
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.gpr, u₉.gpr, u₈.gpr]; exact u₇.gpr)
    (by rw [mem]; exact cv₉) (by rw [mem]; exact w₁) (by rw [mem]; exact w₂)

end VG.Proof.Rc2.X86.Stream.Init

end

/-!
# Streaming RC2-CBC on x86 (32-bit): `init` is correct

The call of the verified key expansion (`keyCall_ok`) and `init_correct`: the
error code for invalid lengths, and otherwise the context.
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

abbrev rs5 : List Reg := [.ebx, .esi, .edx, .ecx, .eax]

theorem key_nosp : NoSp Impl.Rc2.X86.expandKey := NoSp.of_all (by lit_decide)

theorem key_stack : stackUse Impl.Rc2.X86.expandKey = 0 := by decide

def callRd (s₀ s : State) : List Region := [keyR s₀, ⟨argAddr (pushed rs5 s).callEntry 0, 20⟩]
def callWr (s₀ : State) : List Region := [schR s₀, ⟨sA s₀, 512⟩]

theorem setWidth_append (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  have := b.isLt
  omega

/-- What the call of `vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)` needs. -/
theorem keyCallPre_ok {s₀ s : State} (hp : Pre s₀) (hk : 1 ≤ kl s₀ ∧ kl s₀ ≤ 128)
    (he : 1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) (hc : Common s₀ s)
    (eax : s.gpr .eax = key s₀) (ecx : s.gpr .ecx = arg s₀ 1) (edx : s.gpr .edx = arg s₀ 2)
    (esi : s.gpr .esi = ctx s₀) (ebx : s.gpr .ebx = scr s₀) :
    VG.X86.CallPre keyContract rs5 (callRd s₀ s) (callWr s₀) s := by
  have hlo := hp.sp_lo
  have hEf := hp.sp_fit
  have hesp : s.gpr .esp = E s₀ := hc.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  have a0 : arg (pushed rs5 s).callEntry 0 = key s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact eax
  have a1 : arg (pushed rs5 s).callEntry 1 = arg s₀ 1 := by rw [callEntry_arg fit hrs (by simp)]; exact ecx
  have a2 : arg (pushed rs5 s).callEntry 2 = arg s₀ 2 := by rw [callEntry_arg fit hrs (by simp)]; exact edx
  have a3 : arg (pushed rs5 s).callEntry 3 = ctx s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact esi
  have a4 : arg (pushed rs5 s).callEntry 4 = scr s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact ebx
  have eSp : (pushed rs5 s).callEntry.gpr .esp = E s₀ - BitVec.ofNat 32 24 := by
    rw [callEntry_esp', hesp]; rfl
  have eA : argAddr (pushed rs5 s).callEntry 0 = (E s₀ - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  have kA' : Region.Sub ⟨(E s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩ (stkR s₀) := below_sub (by decide) hlo
  have kR : Region.Sub ⟨(E s₀ - BitVec.ofNat 32 24).setWidth 64, 4⟩ (stkR s₀) := by
    have := below_inner (sp := E s₀) (a := 4) (b := 24) (k := 20) (by omega) hlo
    rw [show E s₀ - BitVec.ofNat 32 24 = E s₀ - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have bS : Region.Sub ⟨sA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by decide)
  have wr : s.wr = [ctxR s₀, scR s₀] := hc.wr.trans hp.wr
  have rd : s.rd = [keyR s₀, ivR s₀, argR s₀] := hc.rd.trans hp.rd
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  refine ⟨?_, ?_, ?_⟩
  · simp only [keyContract, callRd, callWr, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, addr32]
    refine ⟨trivial, trivial, hp.k_c.sub_right sch_sub, hp.k_s.sub_right bS,
      (hp.c_s.sub_left sch_sub).sub_right bS, (hp.t_c.sub_left kA').sub_right sch_sub,
      (hp.t_s.sub_left kA').sub_right bS, (hp.t_c.sub_left kR).sub_right sch_sub,
      (hp.t_s.sub_left kR).sub_right bS, hp.k_fit, by have := hp.c_fit; omega,
      by have := hp.s_fit; omega, by rw [sub_toNat (by omega)]; omega, hk.1, hk.2, he.1, he.2⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [callRd, callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨keyR s₀, by simp [rd], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true (by simp)⟩
    · refine ⟨below (s.gpr .esp) (4 * rs5.length), by simp, 0, ?_, by simp⟩
      rw [BitVec.add_zero, callEntry_argAddr0]
    · exact ⟨ctxR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ctxR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩

/-- The call of `vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)`. -/
theorem keyCall_ok {s₀ s : State} (hp : Pre s₀) (hk : 1 ≤ kl s₀ ∧ kl s₀ ≤ 128)
    (he : 1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) (hc : Common s₀ s)
    (eax : s.gpr .eax = key s₀) (ecx : s.gpr .ecx = arg s₀ 1) (edx : s.gpr .edx = arg s₀ 2)
    (esi : s.gpr .esi = ctx s₀) (ebx : s.gpr .ebx = scr s₀) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [schR s₀, ⟨sA s₀, 512⟩, stkR s₀] s.mem s'.mem →
      Spec.Rc2.scheduleAt s'.mem (cA s₀) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s₀.mem (kA s₀) (kl s₀)) (eb s₀) → Q s') :
    WP isa keyCall s Q := by
  have hlo := hp.sp_lo
  have hEf := hp.sp_fit
  have hesp : s.gpr .esp = E s₀ := hc.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  have hesp : s.gpr .esp = E s₀ := hc.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; have := hp.sp_lo; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  have a0 : arg (pushed rs5 s).callEntry 0 = key s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact eax
  have a1 : arg (pushed rs5 s).callEntry 1 = arg s₀ 1 := by rw [callEntry_arg fit hrs (by simp)]; exact ecx
  have a2 : arg (pushed rs5 s).callEntry 2 = arg s₀ 2 := by rw [callEntry_arg fit hrs (by simp)]; exact edx
  have a3 : arg (pushed rs5 s).callEntry 3 = ctx s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact esi
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  refine WP.callWith (k := keyContract) key_body_correct key_nosp (by simp) hrs
    (by rw [key_stack, hesp]; simp only [List.length_cons, List.length_nil]; have := hp.sp_lo; omega)
    (keyCallPre_ok hp hk he hc eax ecx edx esi ebx) fun s' rd' wr' cs f ⟨s₂, m₂, post⟩ => ?_
  · have ce := callEntry_frame fit hrs
    have kE : Region.Sub (below (s.gpr .esp) (4 * rs5.length + 4)) (stkR s₀) := by
      rw [hesp]; exact fun _ h => h
    simp only [keyContract, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, m₂, addr32] at post
    rw [Proof.Rc2.bytesAt_frame ce _ _ (by omega) (sing ((hp.t_k.sub_left kE).symm)),
      Proof.Rc2.bytesAt_frame hc.frame _ _ (by omega) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.k_c.sub_right cv_sub
        · exact hp.k_s)] at post
    refine hQ s' rd' wr' cs (f.sub fun r hr => ?_) post
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨sA s₀, 512⟩, by simp, fun _ h => h⟩
    · refine ⟨stkR s₀, by simp, ?_⟩
      rw [key_stack, hesp]; exact fun _ h => h

theorem code_err {s₀ : State} (h : code s₀ ≠ 0) :
    code s₀ = (if ¬(1 ≤ kl s₀ ∧ kl s₀ ≤ 128) then 1 else if ¬(1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) then 2 else 3) ∧
      ¬((1 ≤ kl s₀ ∧ kl s₀ ≤ 128) ∧ (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) ∧ il s₀ = 8) := by
  unfold code at h ⊢
  by_cases h₁ : 1 ≤ kl s₀ ∧ kl s₀ ≤ 128 <;> by_cases h₂ : 1 ≤ eb s₀ ∧ eb s₀ ≤ 1024 <;>
    by_cases h₃ : il s₀ = 8 <;> simp [h₁, h₂, h₃] at h ⊢

theorem code_ok {s₀ : State} (h : code s₀ = 0) :
    (1 ≤ kl s₀ ∧ kl s₀ ≤ 128) ∧ (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) ∧ il s₀ = 8 := by
  unfold code at h
  by_cases h₁ : 1 ≤ kl s₀ ∧ kl s₀ ≤ 128 <;> by_cases h₂ : 1 ≤ eb s₀ ∧ eb s₀ ≤ 1024 <;>
    by_cases h₃ : il s₀ = 8 <;> simp [h₁, h₂, h₃] at h ⊢ <;> omega

theorem code_lt (s₀ : State) : code s₀ < 4 := by
  unfold code; split <;> [skip; split <;> [skip; split]] <;> decide

theorem init_correct (s₀ : State) (hs : initContract.pre s₀) :
    WP isa init s₀ (fun s' => abiPreserved s₀ s' ∧ initContract.post s₀ s') := by
  have hp := pre_of hs
  rw [init]
  refine WP.seq (checks_ok hp fun s c m a b e => ?_)
  refine WP.seq (wp_test fun s₁ f₁ hz => WP.block_nil ?_)
  have hz' : s₁.zf = some (decide (code s₀ = 0)) := by
    rw [hz, a, BitVec.and_self, ofNat_beq_zero (by have := code_lt s₀; omega)]
  have c₁ := c.fupd f₁
  refine WP.ite (!decide (code s₀ = 0)) (by show s₁.zf.map (!·) = _; rw [hz']; rfl)
    (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · -- Invalid lengths.
    have h0 : code s₀ ≠ 0 := of_decide_eq_false (by revert hb; cases decide (code s₀ = 0) <;> simp)
    obtain ⟨hcode, hbad⟩ := code_err h0
    refine ⟨⟨?_, by rw [f₁.mem, m]⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rw [f₁.gpr]
      exacts [b, e, c.edi, c.ebp, c.esp]
    · refine init_post_error (m := s₀.mem) (m' := s₁.mem) (key := kA s₀) (iv := ivA s₀) (ctx := cA s₀)
        (keyLen := kl s₀) (effectiveBits := eb s₀) (ivLen := il s₀) ?_ hbad
      rw [setWidth_append, f₁.gpr, a, toNat_ofNat_lt (by have := code_lt s₀; omega)]
      exact hcode
  · have h0 : code s₀ = 0 := of_decide_eq_true (by revert hb; cases decide (code s₀ = 0) <;> simp)
    obtain ⟨hk, he, hi⟩ := code_ok h0
    rw [initBody]
    refine WP.seq (initArgs_ok hp hi c₁ (by rw [f₁.mem, m]) (by rw [f₁.gpr]; exact b) (by rw [f₁.gpr]; exact e)
      fun t ct ea ec ed es eb' cv w₁ w₂ => ?_)
    refine WP.seq (keyCall_ok hp hk he ct ea ec ed es eb' fun s' rd' wr' cs f sch => ?_)
    have bS : Region.Sub ⟨sA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by decide)
    have sep3 {r : Region} (h₁ : r.Disjoint (schR s₀)) (h₂ : r.Disjoint ⟨sA s₀, 512⟩) (h₃ : r.Disjoint (stkR s₀)) :
        ∀ x ∈ [schR s₀, ⟨sA s₀, 512⟩, stkR s₀], r.Disjoint x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl)
      exacts [h₁, h₂, h₃]
    have word {d : Nat} (hd : 512 ≤ d) (hd' : d + 4 ≤ 576) :
        s'.mem.readW (addr (scr s₀) d) 32 = t.mem.readW (addr (scr s₀) d) 32 := by
      refine f.readW (Region.contains_self _ _) (sep3 ?_ ?_ ?_) (by decide)
      · exact (hp.c_s.sub_left sch_sub).symm.sub_left (hp.scr_sub hd')
      · rw [hp.scr_addr hd']; exact Offset.disjoint_base _ hd (by omega)
      · exact hp.t_s.symm.sub_left (hp.scr_sub hd')
    have scIn (d : Nat) (hd : d + 4 ≤ 576) : InRegions (s'.rd ++ s'.wr) (addr (scr s₀) d) 4 := by
      rw [wr', ct.wr, hp.wr, hp.scr_addr hd]
      exact ⟨scR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
    have ebx' : s'.gpr .ebx = scr s₀ := by rw [cs _ (by simp [calleeSaved])]; exact eb'
    simp only [restore, List.cons_append, List.nil_append]
    refine wp_ldm (o := 516) ebx' (scIn 516 (by decide)) fun s₂ u₂ => ?_
    refine wp_ldm (o := 512) (B := scr s₀) (by rw [u₂.other _ (by decide)]; exact ebx')
      (by rw [u₂.rd, u₂.wr]; exact scIn 512 (by decide)) fun s₃ u₃ => ?_
    refine wp_movi fun s₄ u₄ => WP.block_nil ?_
    have mem : s₄.mem = s'.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
    have g (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ebx) (h₃ : r ≠ .esi) (hr : r ∈ calleeSaved) :
        s₄.gpr r = t.gpr r := by
      rw [u₄.other _ h₁, u₃.other _ h₂, u₂.other _ h₃]
      exact cs r hr
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, word (by decide) (by decide)]; exact w₁
      · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, word (by decide) (by decide)]; exact w₂
      · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact ct.edi
      · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact ct.ebp
      · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact ct.esp
    · have retStk : (retR s₀).Disjoint (stkR s₀) := by
        show Region.Disjoint ⟨(E s₀).setWidth 64, 4⟩ ⟨(E s₀ - BitVec.ofNat 32 24).setWidth 64, 24⟩
        rw [Taint.sub_setWidth hp.sp_lo]; exact Offset.base_disjoint_below _ (by decide)
      rw [mem, f.readW (Region.contains_self _ _) (sep3 (hp.r_c.sub_right sch_sub) (hp.r_s.sub_right bS) retStk)
        (by decide)]
      refine ct.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.r_c.sub_right cv_sub
      · exact hp.r_s
    · refine init_post (m := s₀.mem) (m' := s₄.mem) (key := kA s₀) (iv := ivA s₀) (ctx := cA s₀)
        (keyLen := kl s₀) (effectiveBits := eb s₀) (ivLen := il s₀) hk he hi ?_ ?_ ?_
      · rw [setWidth_append, u₄.gpr]; rfl
      · rw [mem]; exact sch
      · show Spec.Rc2.blockAt s₄.mem (cA s₀ + BitVec.ofNat 64 128) = _
        rw [mem, Proof.Rc2.blockAt_frame f _ (sep3 sch_cv.symm ((hp.c_s.sub_left cv_sub).sub_right bS)
          (hp.t_c.sub_right cv_sub).symm)]
        exact cv

end VG.Proof.Rc2.X86.Stream.Init
