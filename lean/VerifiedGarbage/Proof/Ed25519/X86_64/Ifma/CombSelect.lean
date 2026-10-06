import VerifiedGarbage.Impl.Ed25519.X86_64.CombIfma
import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Sym

/-!
# Ed25519's comb with AVX512_IFMA: the selection

`vselect` keeps each of the sixteen entries of a table in `ymm11–ymm13`, 32
bytes at a time, under the mask of its magnitude (`vpand`, `vpor`), as
`combSelect` does in `xmm` registers: the accumulators then hold the words
of the entry for the magnitude, or zero.
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519.X86_64
open VG.Impl.X25519.X86_64.Ifma (y v zero)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw qword_and qword_or qw_lane qw_vbin qw_load qw_vmovq
  qw_vpbroadcastq cases4)

/-- What a block leaves of the rest of the state: the general-purpose registers but `rs`, the
memory and the regions, and the quadwords of the vector registers but those of `xs`. -/
structure VKeep (rs : List Reg) (xs : XReg → Prop) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  qw : ∀ r, ¬ xs r → ∀ k < 4, qw t r k = qw s r k
  syms : t.syms = s.syms

theorem VKeep.refl (rs : List Reg) (xs : XReg → Prop) (s : State) : VKeep rs xs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, rfl⟩

theorem VKeep.trans {rs : List Reg} {xs : XReg → Prop} {s₁ s₂ s₃ : State} (h₁ : VKeep rs xs s₁ s₂)
    (h₂ : VKeep rs xs s₂ s₃) : VKeep rs xs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, fun r hr k hk => (h₂.qw r hr k hk).trans (h₁.qw r hr k hk), h₂.syms.trans h₁.syms⟩

theorem VKeep.mono {rs rs' : List Reg} {xs xs' : XReg → Prop} {s t : State} (h : VKeep rs xs s t)
    (hr : ∀ r ∈ rs, r ∈ rs') (hx : ∀ r, xs r → xs' r) : VKeep rs' xs' s t :=
  ⟨fun r h' => h.gpr r fun h'' => h' (hr r h''), h.mem, h.rd, h.wr,
    fun r h' => h.qw r fun h'' => h' (hx r h''), h.syms⟩

theorem y_xr : ∀ n < 16, y n = xr n := by decide

theorem wp_and {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁)
    (h₂ : WP isa c s Q₂) : WP isa c s fun t => Q₁ t ∧ Q₂ t := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

theorem qw_of {s t : State} (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) (r : XReg) (k : Nat) :
    qw t r k = qw s r k := by
  simp only [qw, State.lane, hx, hy]

/-- `rcx` all ones if `r8 = a` is `v`, else zero, keeping the vector registers. -/
theorem vEqMask_ok (s : State) {v a : Nat} (hv : v < 2 ^ 31) (ha : a < 2 ^ 31)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block (combEqMask v)) s fun t => t.gpr .rcx = cmask (decide (a = v)) ∧
      VKeep [.rcx] (fun _ => False) s t := by
  have e : WP isa (.block (combEqMask v)) s fun t => t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
    erun [combEqMask, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags, RegUpd.ymmHi_setReg,
      RegUpd.ymmHi_arithFlags]
  refine WP.mono (wp_and (combEqMask_ok s hv ha h8) e) fun t ⟨⟨c, k, _, y'⟩, x, yh⟩ =>
    ⟨c, ⟨k.1, k.2.1, k.2.2.1, k.2.2.2, fun r _ k _ => qw_of x yh r k, y'⟩⟩

/-- `ymm15` = the mask `rcx` in each quadword. -/
theorem vDupMask_ok (s : State) {b : Bool} (hc : s.gpr .rcx = cmask b) :
    WP isa (.block [.vop (.vmovq (y 15) .rcx), .vop (.vpbroadcastq .l256 (y 15) (y 15))]) s fun t =>
      (∀ k < 4, qw t (xr 15) k = cmask b) ∧ VKeep [] (· = xr 15) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr k hk => ?_, rfl⟩⟩
  · rw [show xr 15 = y 15 from rfl, qw_vpbroadcastq, ite_eq_left rfl, qw_vmovq _ _ _ _ (by decide),
      ite_eq_left rfl, ite_eq_left rfl, hc]
  · rw [qw_vpbroadcastq, ite_eq_right (show r ≠ y 15 from hr), qw_vmovq _ _ _ _ hk,
      ite_eq_right (show r ≠ y 15 from hr)]

/-- Piece `c` of the 32 bytes at `rdx + d`, kept under the mask `ymm15` in `ymm (11 + c)`. -/
theorem vselLoad_ok (s : State) {X : Addr} (hx : s.gpr .rdx = X) {d c : Nat} (hc : c < 3)
    (hr : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 d) 32) :
    WP isa (.block [.vmovdquLoad .l256 (y 10) (combTblAt d), v .vpand 10 10 15,
        v .vpor (11 + c) (11 + c) 10]) s fun t =>
      (∀ k < 4, qw t (xr (11 + c)) k = qw s (xr (11 + c)) k |||
        (s.mem.readW (X + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * k)) 64 &&& qw s (xr 15) k)) ∧
      VKeep [] (fun r => r = xr 10 ∨ r = xr (11 + c)) s t := by
  apply WP.of_runBlock
  simp only [v, runBlock_cons, runStep_some, runBlock_nil, exec, ea_combTblAt, hx, State.load256, hr,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr k hk => ?_, rfl⟩⟩ <;>
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  all_goals first
    | simp only [qw_vbin, VBinOp.sse, XBinOp.eval, qword_or, qword_and, qw_lane, qw_load _ _ _ _ hk, y, xr,
        reduceCtorEq, ↓reduceIte, Nat.reduceAdd]; done
    | (simp only [not_or, xr, Nat.reduceAdd] at hr
       simp only [qw_vbin, qw_load _ _ _ _ hk, y, hr.1, hr.2, ite_false])

/-- The pieces `c < n` of entry `m` of the table at `rdx = X` kept under the mask `ymm15` in
their accumulators. -/
theorem vselLoads_ok {m : Nat} {X : Addr} : ∀ n ≤ 3, ∀ (s : State), s.gpr .rdx = X →
    (∀ c < 3, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 32 * c)) 32) →
    WP isa (.block ((List.range n).flatMap fun c =>
        [.vmovdquLoad .l256 (y 10) (combTblAt (combEntryBytes * (m - 1) + 32 * c)), v .vpand 10 10 15,
          v .vpor (11 + c) (11 + c) 10])) s fun t =>
      (∀ c < 3, ∀ k < 4, qw t (xr (11 + c)) k = if c < n then qw s (xr (11 + c)) k |||
          (s.mem.readW (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 32 * c) + BitVec.ofNat 64 (8 * k)) 64 &&&
            qw s (xr 15) k)
        else qw s (xr (11 + c)) k) ∧
      VKeep [] (fun r => r = xr 10 ∨ ∃ c < 3, r = xr (11 + c)) s t
  | 0, _, s, _, _ => WP.block_nil ⟨fun c _ k _ => by simp, VKeep.refl _ _ _⟩
  | n + 1, hn, s, hx, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (vselLoads_ok n (by omega) s hx hr) fun s₁ ⟨a₁, k₁⟩ => ?_
    have h15 : ∀ k < 4, qw s₁ (xr 15) k = qw s (xr 15) k := k₁.qw _ (by
      rintro (h | ⟨c, hc, h⟩)
      · exact absurd h (by decide)
      · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> exact absurd h (by decide))
    refine WP.mono (vselLoad_ok s₁ ((k₁.gpr _ List.not_mem_nil).trans hx) (c := n) (by omega)
      (by rw [k₁.rd, k₁.wr]; exact hr n (by omega))) fun t ⟨a₂, k₂⟩ => ⟨fun c hc k hk => ?_, ?_⟩
    · by_cases hcn : c = n
      · subst hcn
        rw [a₂ k hk, a₁ c hc k hk, h15 k hk, k₁.mem]
        simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self]
      · rw [k₂.qw _ (by
          rintro (h | h)
          · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> exact absurd h (by decide)
          · exact hcn (by
              rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
              rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;>
              first | rfl | exact absurd h (by decide))) k hk, a₁ c hc k hk]
        by_cases hlt : c < n
        · simp only [hlt, show c < n + 1 by omega, ↓reduceIte]
        · simp only [hlt, show ¬ c < n + 1 by omega, ↓reduceIte]
    · exact k₁.trans (k₂.mono (fun _ h => h) fun r h => by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨n, by omega, h⟩)

/-- Accumulator `c`'s quadword `k` after the entries `1 … m` for the magnitude `a`: that of
entry `a` of the table at `X` if `1 ≤ a ≤ m`, else zero. -/
def accQ (mem : Mem) (X : Addr) (a m c k : Nat) : BitVec 64 :=
  if 1 ≤ a ∧ a ≤ m then
    mem.readW (X + BitVec.ofNat 64 (combEntryBytes * (a - 1) + 32 * c) + BitVec.ofNat 64 (8 * k)) 64
  else 0

theorem accQ_step (mem : Mem) (X : Addr) (a m c k : Nat) (hm : 1 ≤ m) :
    accQ mem X a (m - 1) c k |||
      (mem.readW (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 32 * c) + BitVec.ofNat 64 (8 * k)) 64 &&&
        cmask (decide (a = m))) = accQ mem X a m c k := by
  unfold accQ
  by_cases h : a = m
  · subst h
    rw [decide_eq_true rfl, show cmask true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes,
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true ⟨hm, Nat.le_refl _⟩)]
    simp
  · rw [decide_eq_false h, show cmask false = 0 from rfl]
    have e : ∀ x y : BitVec 64, x ||| (y &&& 0) = x := fun x y => by simp
    rw [e]
    by_cases h' : 1 ≤ a ∧ a ≤ m - 1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- The registers the selection writes. -/
abbrev selRegs (r : XReg) : Prop := r = xr 10 ∨ (∃ c < 3, r = xr (11 + c)) ∨ r = xr 15

/-- Entry `m` of the table at `rdx = X` kept in the accumulators under the mask of `r8 = a`. -/
theorem vselEntry_ok {s : State} {X : Addr} {a m : Nat} (hm1 : 1 ≤ m)
    (hm : m < 2 ^ 31) (ha : a < 2 ^ 31) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hx : s.gpr .rdx = X)
    (hr : ∀ c < 3, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 32 * c)) 32)
    (hacc : ∀ c < 3, ∀ k < 4, qw s (xr (11 + c)) k = accQ s.mem X a (m - 1) c k) :
    WP isa (.block (vselEntry m)) s fun t =>
      (∀ c < 3, ∀ k < 4, qw t (xr (11 + c)) k = accQ s.mem X a m c k) ∧ VKeep [.rcx] selRegs s t := by
  rw [vselEntry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (vEqMask_ok s hm ha h8) fun s₁ ⟨c₁, k₁⟩ => ?_
  refine WP.mono (vDupMask_ok s₁ c₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have hx₂ : s₂.gpr .rdx = X := by rw [k₂.gpr _ List.not_mem_nil, k₁.gpr _ (by decide), hx]
  have hm₂ : s₂.mem = s.mem := k₂.mem.trans k₁.mem
  refine WP.mono (vselLoads_ok 3 (Nat.le_refl _) s₂ hx₂ (by
      rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hr)) fun t ⟨a₃, k₃⟩ => ⟨fun c hc k hk => ?_, ?_⟩
  · have hne : xr (11 + c) ≠ xr 15 := by
      rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide
    rw [a₃ c hc k hk, ite_eq_left_of_eq_true _ _ (eq_true hc), x₂ k hk, hm₂,
      k₂.qw _ hne k hk, k₁.qw _ id k hk, hacc c hc k hk]
    exact accQ_step _ _ _ _ _ _ hm1
  · refine ⟨fun r hr => ?_, k₃.mem.trans hm₂, by rw [k₃.rd, k₂.rd, k₁.rd],
      by rw [k₃.wr, k₂.wr, k₁.wr], fun r hr k hk => ?_, by rw [k₃.syms, k₂.syms, k₁.syms]⟩
    · rw [k₃.gpr r List.not_mem_nil, k₂.gpr r List.not_mem_nil, k₁.gpr r hr]
    · simp only [selRegs, not_or] at hr
      rw [k₃.qw r (by rintro (h | h); exacts [hr.1 h, hr.2.1 h]) k hk, k₂.qw r hr.2.2 k hk,
        k₁.qw r id k hk]

/-- The entries `1 … n` of the table at `rdx = X` kept in the cleared accumulators under the
masks of `r8 = a`. -/
theorem vselEntries_ok {X : Addr} {a : Nat} (ha : a < 2 ^ 31) :
    ∀ n, n < 2 ^ 31 → ∀ (s : State), s.gpr .r8 = BitVec.ofNat 64 a → s.gpr .rdx = X →
    (∀ e < n, ∀ c < 3, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * e + 32 * c)) 32) →
    (∀ c < 3, ∀ k < 4, qw s (xr (11 + c)) k = 0) →
    WP isa (.block ((List.range n).flatMap fun m => vselEntry (m + 1))) s fun t =>
      (∀ c < 3, ∀ k < 4, qw t (xr (11 + c)) k = accQ s.mem X a n c k) ∧ VKeep [.rcx] selRegs s t
  | 0, _, s, _, _, _, h0 => WP.block_nil ⟨fun c hc k hk => by
      rw [h0 c hc k hk, accQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega))], VKeep.refl _ _ _⟩
  | n + 1, hn, s, h8, hx, hr, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (vselEntries_ok ha n (by omega) s h8 hx (fun e he => hr e (by omega)) h0)
      fun s₁ ⟨a₁, k₁⟩ => ?_
    refine WP.mono (vselEntry_ok (X := X) (m := n + 1) (by omega) hn ha
      (by rw [k₁.gpr _ (by decide), h8]) (by rw [k₁.gpr _ (by decide), hx])
      (fun c hc => by rw [k₁.rd, k₁.wr, Nat.add_sub_cancel]; exact hr n (by omega) c hc)
      (fun c hc k hk => by rw [a₁ c hc k hk, k₁.mem, Nat.add_sub_cancel])) fun t ⟨a₂, k₂⟩ =>
      ⟨fun c hc k hk => by rw [a₂ c hc k hk, k₁.mem], k₁.trans k₂⟩

theorem qword_zero (i : Nat) : qword (0 : BitVec 128) i = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword]

/-- `ymm11–ymm13` cleared. -/
theorem vselClear_ok (s : State) :
    WP isa (.block [zero 11, zero 12, zero 13]) s fun t =>
      (∀ c < 3, ∀ k < 4, qw t (xr (11 + c)) k = 0) ∧ VKeep [] selRegs s t := by
  apply WP.of_runBlock
  simp only [zero, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun c hc k hk => ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr k hk => ?_, rfl⟩⟩
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
      simp only [qw_vbin, VBinOp.sse, XBinOp.eval, BitVec.xor_self, y, xr, Nat.reduceAdd, reduceCtorEq,
        ↓reduceIte] <;> exact qword_zero _
  · simp only [selRegs, not_or, not_exists, not_and] at hr
    have h1 := hr.2.1 0 (by decide); have h2 := hr.2.1 1 (by decide); have h3 := hr.2.1 2 (by decide)
    simp only [Nat.reduceAdd] at h1 h2 h3
    simp only [qw_vbin, show y 11 = xr 11 from rfl, show y 12 = xr 12 from rfl,
      show y 13 = xr 13 from rfl, h1, h2, h3, ite_false]

/-- The selection: the words of entry `a ≤ 16` of table `j < 26` (`combCached`, but its `2Z`) in
`ymm11–ymm13` if `a ≠ 0`, else zero. -/
theorem vselect_ok {s : State} {T : Addr} (ht : CombTbl s T) {j a : Nat} (hj : j < 26) (ha : a ≤ 16)
    (hd : s.gpr .rdx = BitVec.ofNat 64 j) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block vselect) s fun t =>
      (∀ c < 3, ∀ k < 4, qw t (xr (11 + c)) k = if 1 ≤ a then feWord (combField j a c) k else 0) ∧
      VKeep [.rax, .rcx, .rdx] selRegs s t := by
  have hsetup : WP isa (.block combSelSetup) s fun t => t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
    erun [combSelSetup, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags, RegUpd.ymmHi_setReg,
      RegUpd.ymmHi_arithFlags, RegUpd.xmm_setFlags, RegUpd.ymmHi_setFlags]
  rw [vselect, List.append_assoc, WP.block_append_iff]
  refine WP.mono (wp_and (combSelSetup_ok s hd ht.sym) hsetup) fun s₁ ⟨⟨x₁, k₁, _, y₁⟩, xx, yy⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vselClear_ok s₁) fun s₂ ⟨a₂, k₂⟩ => ?_
  have hr : ∀ e < 16, ∀ c < 3, InRegions (s₂.rd ++ s₂.wr)
      (T + BitVec.ofNat 64 (j * combTblBytes) + BitVec.ofNat 64 (combEntryBytes * e + 32 * c)) 32 := by
    intro e he c hc
    rw [k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine VG.CallLay.inRegions_sub ht.rd ?_ (by decide)
    simp only [combTblBytes, combEntryBytes, combWordCount]; omega
  refine WP.mono (vselEntries_ok (X := T + BitVec.ofNat 64 (j * combTblBytes)) (a := a) (by omega) 16 (by decide) s₂
    (by rw [k₂.gpr _ List.not_mem_nil, k₁.1 _ (by decide), h8])
    (by rw [k₂.gpr _ List.not_mem_nil, x₁]) hr a₂) fun t ⟨a₃, k₃⟩ => ⟨fun c hc k hk => ?_, ?_⟩
  · rw [a₃ c hc k hk, accQ, k₂.mem, k₁.2.1]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩), ite_eq_left_of_eq_true _ _ (eq_true h1)]
      have hw := combTbl_word ht hj h1 ha (i := 4 * c + k) (by omega)
      rw [Proof.X25519.X86_64.word, Proof.X25519.X86_64.off] at hw
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        show combEntryBytes * (a - 1) + 32 * c + 8 * k = combEntryBytes * (a - 1) + 8 * (4 * c + k) by omega,
        hw, entryWords_getD _ c k hc hk, combField, combCached_succ j a h1]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h1)]
  · refine ⟨fun r hr => ?_, by rw [k₃.mem, k₂.mem, k₁.2.1], by rw [k₃.rd, k₂.rd, k₁.2.2.1],
      by rw [k₃.wr, k₂.wr, k₁.2.2.2], fun r hr k hk => ?_, by rw [k₃.syms, k₂.syms, y₁]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [k₃.gpr r (by simp [hr.2.1]), k₂.gpr r List.not_mem_nil, k₁.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)]
    · rw [k₃.qw r hr k hk, k₂.qw r hr k hk, qw_of xx yy]

end VG.Proof.Ed25519.X86_64.Ifma
