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
  qw_vpbroadcastq cases4 qword_eq qword_ofDwords qword256_eq qw_setV256 qw_setV128)

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

/-- `a` in both doublewords of a quadword. -/
abbrev dup32 (a : Nat) : BitVec 64 := BitVec.ofNat 32 a ++ BitVec.ofNat 32 a

theorem app32_lo (a b : BitVec 32) : (a ++ b).extractLsb' 0 32 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

theorem app32_hi (a b : BitVec 32) : (a ++ b).extractLsb' 32 32 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

/-- The doublewords of a quadword holding `A` in both. -/
theorem dwords_of_qword {x : BitVec 128} {i : Nat} {A : BitVec 32} (h : qword x i = A ++ A) :
    dword x (2 * i) = A ∧ dword x (2 * i + 1) = A := by
  rw [qword_eq] at h
  have h0 := congrArg (BitVec.extractLsb' 0 32) h
  have h1 := congrArg (BitVec.extractLsb' 32 32) h
  rw [app32_lo, app32_lo] at h0
  rw [app32_hi, app32_hi] at h1
  exact ⟨h0, h1⟩

/-- `pcmpeqd` of quadwords holding `A` and `B` in both doublewords: all ones exactly for
`A = B`. -/
theorem qword_pcmpeqd {x y : BitVec 128} {i : Nat} (hi : i < 2) {A B : BitVec 32}
    (hx : qword x i = A ++ A) (hy : qword y i = B ++ B) :
    qword (XBinOp.eval .pcmpeqd x y) i = cmask (decide (A = B)) := by
  obtain ⟨x0, x1⟩ := dwords_of_qword hx
  obtain ⟨y0, y1⟩ := dwords_of_qword hy
  simp only [XBinOp.eval]
  rw [qword_ofDwords _ _ _ _ hi]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.reduceMul, Nat.reduceAdd] at x0 x1 y0 y1 <;>
    simp only [x0, x1, y0, y1, ↓reduceIte, Nat.one_ne_zero] <;>
    by_cases h : A = B <;> simp only [h, ↓reduceIte, decide_true, decide_false] <;> decide

theorem ofNat32_eq {a m : Nat} (ha : a < 2 ^ 32) (hm : m < 2 ^ 32) :
    decide (BitVec.ofNat 32 a = BitVec.ofNat 32 m) = decide (a = m) := by
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hm] at this
  exact this

theorem ea_combMagAt (s : State) (m : Nat) :
    s.ea (combMagAt m) = s.gpr .rax + BitVec.ofNat 64 (combMagBytes + 32 * (m - 1)) := by
  simp only [State.ea, combMagAt, BitVec.ofInt_natCast]

/-- Quadword `k` of a 256-bit load, through its lane. -/
theorem qword_load256 (mem : Mem) (a : Addr) {k : Nat} (hk : k < 4) :
    qword ((mem.readW a 256).extractLsb' (128 * (k / 2)) 128) (k % 2) =
      mem.readW (a + BitVec.ofNat 64 (8 * k)) 64 := by
  rw [← qword256_eq, qword256, show 64 * k = 8 * (8 * k) by omega]
  exact readW_extract _ _ (k := 8 * k) (n := 8) (by omega)

/-- `ymm15` = the mask of `a = m` in every quadword: `vpcmpeqd` of `ymm14`, `a` in every
doubleword, with the 32 bytes of the magnitude `m` in the static at `rax`. -/
theorem vMagMask_ok (s : State) {S : Addr} (hax : s.gpr .rax = S) {a m : Nat} (ha : a < 2 ^ 32)
    (hm : m < 2 ^ 32) (h14 : ∀ k < 4, qw s (xr 14) k = dup32 a)
    (hr : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (combMagBytes + 32 * (m - 1))) 32)
    (hv : ∀ k < 4, s.mem.readW (S + BitVec.ofNat 64 (combMagBytes + 32 * (m - 1)) + BitVec.ofNat 64 (8 * k)) 64 =
      dup32 m) :
    WP isa (.block [.vbinLoad .vpcmpeqd .l256 (y 15) (y 14) (combMagAt m)]) s fun t =>
      (∀ k < 4, qw t (xr 15) k = cmask (decide (a = m))) ∧ VKeep [] (· = xr 15) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_combMagAt, hax, State.load256, hr,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr k hk => ?_, rfl⟩⟩
  · rw [show xr 15 = y 15 from rfl, qw_setV256, ite_eq_left rfl]
    have e : (if k / 2 = 0 then
          (VBinOp.vpcmpeqd).sse.eval (s.lane (y 14) 0) ((s.mem.readW (S + BitVec.ofNat 64
            (combMagBytes + 32 * (m - 1))) 256).extractLsb' 0 128)
        else (VBinOp.vpcmpeqd).sse.eval (s.lane (y 14) 1) ((s.mem.readW (S + BitVec.ofNat 64
            (combMagBytes + 32 * (m - 1))) 256).extractLsb' 128 128)) =
        XBinOp.eval .pcmpeqd (s.lane (y 14) (k / 2)) ((s.mem.readW (S + BitVec.ofNat 64
          (combMagBytes + 32 * (m - 1))) 256).extractLsb' (128 * (k / 2)) 128) := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
    rw [e, qword_pcmpeqd (Nat.mod_lt _ (by decide)) (by rw [qw_lane]; exact h14 k hk)
      (by rw [qword_load256 _ _ hk]; exact hv k hk), ofNat32_eq ha hm]
  · rw [qw_setV256, ite_eq_right (show r ≠ y 15 from hr)]

/-- `rax` = the static's address `T`, and `ymm14` = the magnitude `r8 = a` in every doubleword. -/
theorem vselMag_ok (s : State) {T : Addr} (hT : s.syms combSym = T) {a : Nat} (ha : a < 2 ^ 32)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block vselMag) s fun t => t.gpr .rax = T ∧ (∀ k < 4, qw t (xr 14) k = dup32 a) ∧
      VKeep [.rax] (· = xr 14) s t := by
  have hd : dword ((0 : BitVec 64) ++ BitVec.ofNat 64 a) 0 = BitVec.ofNat 32 a := by
    apply BitVec.eq_of_toNat_eq
    simp only [dword_eq, BitVec.extractLsb'_toNat, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mul_zero,
      Nat.shiftRight_zero, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or]
    rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt ha]
  apply WP.of_runBlock
  simp only [vselMag, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨by simp only [VOp.exec_gpr, RegUpd.gpr_setReg, ite_true, hT], fun k hk => ?_,
    ⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr k hk => ?_, ?_⟩⟩
  · rw [show xr 14 = y 14 from rfl]
    simp only [VOp.exec]
    rw [qw_setV256, ite_eq_left rfl, ite_self, qword_ofDwords _ _ _ _ (Nat.mod_lt _ (by decide)), ite_self]
    simp only [State.setV, ↓reduceIte, RegUpd.gpr_setReg, reduceCtorEq, h8, hd]
  · simp only [List.mem_singleton] at hr
    simp only [VOp.exec_gpr, RegUpd.gpr_setReg, hr, ite_false]
  · simp only [VOp.exec_mem, RegUpd.mem_setReg]
  · simp only [VOp.exec_rd, RegUpd.rd_setReg]
  · simp only [VOp.exec_wr, RegUpd.wr_setReg]
  · simp only [VOp.exec]
    rw [qw_setV256, ite_eq_right (show r ≠ y 14 from hr), qw_setV128, ite_eq_right (show r ≠ y 14 from hr)]
    rfl
  · rfl

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

/-- The registers an entry writes. -/
abbrev entryRegs (r : XReg) : Prop := r = xr 10 ∨ (∃ c < 3, r = xr (11 + c)) ∨ r = xr 15

/-- The registers the selection writes. -/
abbrev selRegs (r : XReg) : Prop := entryRegs r ∨ r = xr 14

/-- What the entries read of the magnitudes in the static at `S`: the 32 bytes of each `m ≤ n`
readable, holding `m` in every doubleword. -/
def MagsAt (s : State) (S : Addr) (n : Nat) : Prop :=
  ∀ m, 1 ≤ m → m ≤ n → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (combMagBytes + 32 * (m - 1))) 32 ∧
    ∀ k < 4, s.mem.readW (S + BitVec.ofNat 64 (combMagBytes + 32 * (m - 1)) + BitVec.ofNat 64 (8 * k)) 64 =
      dup32 m

/-- Entry `m` of the table at `rdx = X` kept in the accumulators under the mask of the magnitude
`a` in `ymm14`. -/
theorem vselEntry_ok {s : State} {X S : Addr} {a m : Nat} (hm1 : 1 ≤ m)
    (hm : m < 2 ^ 32) (ha : a < 2 ^ 32) (hax : s.gpr .rax = S) (h14 : ∀ k < 4, qw s (xr 14) k = dup32 a)
    (hmag : MagsAt s S m) (hx : s.gpr .rdx = X)
    (hr : ∀ c < 3, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 32 * c)) 32)
    (hacc : ∀ c < 3, ∀ k < 4, qw s (xr (11 + c)) k = accQ s.mem X a (m - 1) c k) :
    WP isa (.block (vselEntry m)) s fun t =>
      (∀ c < 3, ∀ k < 4, qw t (xr (11 + c)) k = accQ s.mem X a m c k) ∧ VKeep [] entryRegs s t := by
  rw [vselEntry, WP.block_append_iff]
  obtain ⟨hmr, hmv⟩ := hmag m hm1 (Nat.le_refl _)
  refine WP.mono (vMagMask_ok s hax ha hm h14 hmr hmv) fun s₂ ⟨x₂, k₂⟩ => ?_
  have hx₂ : s₂.gpr .rdx = X := by rw [k₂.gpr _ List.not_mem_nil, hx]
  refine WP.mono (vselLoads_ok 3 (Nat.le_refl _) s₂ hx₂ (by
      rw [k₂.rd, k₂.wr]; exact hr)) fun t ⟨a₃, k₃⟩ => ⟨fun c hc k hk => ?_, ?_⟩
  · have hne : xr (11 + c) ≠ xr 15 := by
      rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide
    rw [a₃ c hc k hk, ite_eq_left_of_eq_true _ _ (eq_true hc), x₂ k hk, k₂.mem,
      k₂.qw _ hne k hk, hacc c hc k hk]
    exact accQ_step _ _ _ _ _ _ hm1
  · refine ⟨fun r hr => ?_, k₃.mem.trans k₂.mem, by rw [k₃.rd, k₂.rd],
      by rw [k₃.wr, k₂.wr], fun r hr k hk => ?_, by rw [k₃.syms, k₂.syms]⟩
    · rw [k₃.gpr r List.not_mem_nil, k₂.gpr r hr]
    · simp only [entryRegs, not_or] at hr
      rw [k₃.qw r (by rintro (h | h); exacts [hr.1 h, hr.2.1 h]) k hk, k₂.qw r hr.2.2 k hk]

/-- The entries `1 … n` of the table at `rdx = X` kept in the cleared accumulators under the
masks of the magnitude `a` in `ymm14`. -/
theorem vselEntries_ok {X S : Addr} {a : Nat} (ha : a < 2 ^ 32) :
    ∀ n, n < 2 ^ 32 → ∀ (s : State), s.gpr .rax = S → (∀ k < 4, qw s (xr 14) k = dup32 a) →
    MagsAt s S n → s.gpr .rdx = X →
    (∀ e < n, ∀ c < 3, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * e + 32 * c)) 32) →
    (∀ c < 3, ∀ k < 4, qw s (xr (11 + c)) k = 0) →
    WP isa (.block ((List.range n).flatMap fun m => vselEntry (m + 1))) s fun t =>
      (∀ c < 3, ∀ k < 4, qw t (xr (11 + c)) k = accQ s.mem X a n c k) ∧ VKeep [] entryRegs s t
  | 0, _, s, _, _, _, _, _, h0 => WP.block_nil ⟨fun c hc k hk => by
      rw [h0 c hc k hk, accQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega))], VKeep.refl _ _ _⟩
  | n + 1, hn, s, hax, h14, hmag, hx, hr, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (vselEntries_ok ha n (by omega) s hax h14 (fun m h1 hm => hmag m h1 (by omega)) hx
      (fun e he => hr e (by omega)) h0) fun s₁ ⟨a₁, k₁⟩ => ?_
    have h14₁ : ∀ k < 4, qw s₁ (xr 14) k = dup32 a := fun k hk => by
      rw [k₁.qw _ (by decide) k hk, h14 k hk]
    refine WP.mono (vselEntry_ok (X := X) (S := S) (m := n + 1) (by omega) hn ha
      (by rw [k₁.gpr _ List.not_mem_nil, hax]) h14₁
      (fun m h1 hm => by rw [k₁.rd, k₁.wr, k₁.mem]; exact hmag m h1 hm)
      (by rw [k₁.gpr _ List.not_mem_nil, hx])
      (fun c hc => by rw [k₁.rd, k₁.wr, Nat.add_sub_cancel]; exact hr n (by omega) c hc)
      (fun c hc k hk => by rw [a₁ c hc k hk, k₁.mem, Nat.add_sub_cancel])) fun t ⟨a₂, k₂⟩ =>
      ⟨fun c hc k hk => by rw [a₂ c hc k hk, k₁.mem], k₁.trans k₂⟩

theorem qword_zero (i : Nat) : qword (0 : BitVec 128) i = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword]

/-- `ymm11–ymm13` cleared. -/
theorem vselClear_ok (s : State) :
    WP isa (.block [zero 11, zero 12, zero 13]) s fun t =>
      (∀ c < 3, ∀ k < 4, qw t (xr (11 + c)) k = 0) ∧ VKeep [] entryRegs s t := by
  apply WP.of_runBlock
  simp only [zero, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun c hc k hk => ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr k hk => ?_, rfl⟩⟩
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
      simp only [qw_vbin, VBinOp.sse, XBinOp.eval, BitVec.xor_self, y, xr, Nat.reduceAdd, reduceCtorEq,
        ↓reduceIte] <;> exact qword_zero _
  · simp only [entryRegs, not_or, not_exists, not_and] at hr
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
  rw [vselect, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (wp_and (combSelSetup_ok s hd ht.sym) hsetup) fun s₁ ⟨⟨x₁, k₁, _, y₁⟩, xx, yy⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vselMag_ok s₁ (T := T) (by rw [y₁]; exact ht.sym) (a := a) (by omega)
    (by rw [k₁.1 _ (by decide), h8])) fun s₁' ⟨ax', m₁', k₁'⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vselClear_ok s₁') fun s₂ ⟨a₂, k₂⟩ => ?_
  have hrd : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [k₂.rd, k₂.wr, k₁'.rd, k₁'.wr, k₁.2.2.1, k₁.2.2.2]
  have hmem : s₂.mem = s.mem := by rw [k₂.mem, k₁'.mem, k₁.2.1]
  have hr : ∀ e < 16, ∀ c < 3, InRegions (s₂.rd ++ s₂.wr)
      (T + BitVec.ofNat 64 (j * combTblBytes) + BitVec.ofNat 64 (combEntryBytes * e + 32 * c)) 32 := by
    intro e he c hc
    rw [hrd, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine VG.CallLay.inRegions_sub ht.rd ?_ (by decide)
    simp only [combTblBytes, combEntryBytes, combWordCount]; omega
  have hmag : MagsAt s₂ T 16 := fun m h1 hm => ⟨by
      rw [hrd]
      refine VG.CallLay.inRegions_sub ht.rd ?_ (by decide)
      simp only [combMagBytes, combWordCount]; omega,
    fun k hk => by
      rw [hmem, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        show combMagBytes + 32 * (m - 1) + 8 * k = 8 * (4992 + (4 * (m - 1) + k)) by
          simp only [combMagBytes]; omega,
        ht.val _ (by simp only [combWordCount]; omega), combWords_mag h1 hm hk]⟩
  refine WP.mono (vselEntries_ok (X := T + BitVec.ofNat 64 (j * combTblBytes)) (S := T) (a := a) (by omega)
    16 (by decide) s₂ (by rw [k₂.gpr _ List.not_mem_nil, ax'])
    (fun k hk => by rw [k₂.qw _ (by decide) k hk, m₁' k hk])
    hmag (by rw [k₂.gpr _ List.not_mem_nil, k₁'.gpr _ (by decide), x₁]) hr a₂) fun t ⟨a₃, k₃⟩ =>
    ⟨fun c hc k hk => ?_, ?_⟩
  · rw [a₃ c hc k hk, accQ, hmem]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩), ite_eq_left_of_eq_true _ _ (eq_true h1)]
      have hw := combTbl_word ht hj h1 ha (i := 4 * c + k) (by omega)
      rw [Proof.X25519.X86_64.word, Proof.X25519.X86_64.off] at hw
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        show combEntryBytes * (a - 1) + 32 * c + 8 * k = combEntryBytes * (a - 1) + 8 * (4 * c + k) by omega,
        hw, entryWords_getD _ c k hc hk, combField, combCached_succ j a h1]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h1)]
  · refine ⟨fun r hr => ?_, by rw [k₃.mem, hmem], by rw [k₃.rd, k₂.rd, k₁'.rd, k₁.2.2.1],
      by rw [k₃.wr, k₂.wr, k₁'.wr, k₁.2.2.2], fun r hr k hk => ?_, by rw [k₃.syms, k₂.syms, k₁'.syms, y₁]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [k₃.gpr r List.not_mem_nil, k₂.gpr r List.not_mem_nil, k₁'.gpr r (by simp [hr.1]), k₁.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)]
    · obtain ⟨he, h14⟩ : ¬ entryRegs r ∧ r ≠ xr 14 := not_or.mp hr
      rw [k₃.qw r he k hk, k₂.qw r he k hk, k₁'.qw r h14 k hk, qw_of xx yy]

end VG.Proof.Ed25519.X86_64.Ifma
