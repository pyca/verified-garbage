import VerifiedGarbage.Proof.Bignum.X86_64.AmmCore
import VerifiedGarbage.Proof.Bignum.X86_64.Words

/-!
# RSA with AVX512_IFMA on x86-64: the multiplication's result

After the loop, `ammCore` stores the five accumulators of each prime at
`r11` (and `r11 + D`), then carries the twenty limbs of each in order
(`carryOut`), the two chains interleaved: each limb keeps its low 52 bits
and passes the rest on. `stores_ok` and `carry_ok` give the memory after
each, as numbers (`Amm52.carried`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside ofs_off writeW_outside word_writeW_self)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 carryOut mask52)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw qword256_ymm)

/-! ## Writes of 32 bytes -/

/-- Writes `(e, v)` at `B + e`, the first first. -/
def wrList (m : Mem) (B : Addr) : List (Nat × BitVec 256) → Mem
  | [] => m
  | (e, v) :: rest => wrList (m.writeW (off B e) v) B rest

theorem writeW256_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 256) (h : d + 32 ≤ 2 ^ 64) :
    Outside base d 32 m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- A word that no write of the list touches. -/
theorem word_wrList_other (B : Addr) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem) {d : Nat}, d + 8 ≤ 2 ^ 63 →
      (∀ x ∈ l, x.1 + 32 ≤ 2 ^ 63 ∧ (d + 8 ≤ x.1 ∨ x.1 + 32 ≤ d)) → word (wrList m B l) B d = word m B d
  | [], _, _, _, _ => rfl
  | (e, v) :: rest, m, d, hd, h => by
    have he := h (e, v) (List.mem_cons_self ..)
    rw [wrList, word_wrList_other B rest _ hd fun x hx => h x (List.mem_cons_of_mem _ hx)]
    exact (writeW256_outside m B v (by omega)).word (by omega) (by omega)

/-- The word at `e + 8 t` of the write `(e, v)`, after writes elsewhere. -/
theorem word_wrList_hit (B : Addr) (m : Mem) (l₁ l₂ : List (Nat × BitVec 256)) {e t : Nat} (v : BitVec 256)
    (ht : t < 4) (he : e + 32 ≤ 2 ^ 63)
    (h : ∀ x ∈ l₂, x.1 + 32 ≤ 2 ^ 63 ∧ (e + 8 * t + 8 ≤ x.1 ∨ x.1 + 32 ≤ e + 8 * t)) :
    word (wrList m B (l₁ ++ (e, v) :: l₂)) B (e + 8 * t) = v.extractLsb' (64 * t) 64 := by
  induction l₁ generalizing m with
  | nil =>
    rw [List.nil_append, wrList, word_wrList_other B l₂ _ (by omega) h]
    have := readW_writeW_inside m (off B e) v (k := 8 * t) (n := 8) (by omega) (by decide)
    simp only [word, off] at this ⊢
    rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, this, show 8 * (8 * t) = 64 * t by omega]
  | cons x l₁ ih => exact ih _

/-! ## The stores -/

/-- 32-byte stores of registers at `b` plus offsets. -/
def storeCode (b : Reg) (l : List (Nat × XReg)) : List Instr :=
  l.map fun x => .vmovdquStore .l256 (VG.Impl.Rsa.X86_64.CrtIfma.at_ b x.1) x.2

theorem stores_gen {B : Addr} {b : Reg} :
    ∀ (l : List (Nat × XReg)) (s : State), s.gpr b = B →
      (∀ x ∈ l, InRegions s.wr (off B x.1) 32) →
      WP isa (.block (storeCode b l)) s fun s' => s' = { s with mem := wrList s.mem B (l.map fun x => (x.1, s.ymm x.2)) }
  | [], s, _, _ => WP.block_nil rfl
  | (e, r) :: rest, s, hB, hw => by
    rw [storeCode, List.map_cons, WP.block_cons_iff]
    have ea : s.ea (VG.Impl.Rsa.X86_64.CrtIfma.at_ b e) = off B e := by
      simp only [State.ea, VG.Impl.Rsa.X86_64.CrtIfma.at_, hB, off]
      exact congrArg _ (BitVec.ofInt_natCast ..)
    refine ⟨{ s with mem := s.mem.writeW (off B e) (s.ymm r) }, ?_, ?_⟩
    · simp only [exec, ea, State.store256, hw (e, r) (List.mem_cons_self ..), ite_true]
    · refine WP.mono (stores_gen rest _ hB fun x hx => hw x (List.mem_cons_of_mem _ hx)) fun s' h => ?_
      rw [h]
      rfl

/-- The accumulators' stores of `ammCore`. -/
def accStores : List (Nat × XReg) :=
  (List.range 2).flatMap fun p => (List.range 5).map fun k => (D * p + 32 * k, VG.Impl.Rsa.X86_64.CrtIfma.acc p k 0)

theorem accStores_code :
    ((List.range 2).flatMap fun p => (List.range 5).map fun k =>
      (Instr.vmovdquStore .l256 (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (D * p + 32 * k))
        (VG.Impl.Rsa.X86_64.CrtIfma.acc p k 0))) = storeCode .r11 accStores := by
  decide

/-- The word at `e + 8 t` after writes of which only `(e, v)` touch it. -/
theorem word_wrList_unique (B : Addr) {e t : Nat} {v : BitVec 256} (ht : t < 4) (he : e + 32 ≤ 2 ^ 63) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (e, v) ∈ l →
      (∀ x ∈ l, x.1 + 32 ≤ 2 ^ 63 ∧ (x.1 = e ∨ e + 32 ≤ x.1 ∨ x.1 + 32 ≤ e)) → (∀ x ∈ l, x.1 = e → x.2 = v) →
      word (wrList m B l) B (e + 8 * t) = v.extractLsb' (64 * t) 64
  | [], _, h, _, _ => absurd h (List.not_mem_nil)
  | (e', v') :: rest, m, hm, hd, hv => by
    by_cases hr : (e, v) ∈ rest
    · rw [wrList]
      exact word_wrList_unique B ht he rest _ hr (fun x hx => hd x (List.mem_cons_of_mem _ hx))
        (fun x hx => hv x (List.mem_cons_of_mem _ hx))
    · have h0 : (e, v) = (e', v') := by
        rcases List.mem_cons.1 hm with h | h
        · exact h
        · exact absurd h hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
      have := word_wrList_hit B m [] rest (e := e) (t := t) v ht he (fun x hx => by
        refine ⟨(hd x (List.mem_cons_of_mem _ hx)).1, ?_⟩
        rcases (hd x (List.mem_cons_of_mem _ hx)).2 with h | h | h
        · exact absurd (by rw [← hv x (List.mem_cons_of_mem _ hx) h]; exact h ▸ hx) hr
        · omega
        · omega)
      simpa only [List.nil_append] using this

theorem acc_xr : ∀ p < 2, ∀ k < 5, VG.Impl.Rsa.X86_64.CrtIfma.acc p k 0 = xr (regOf p k 0) := by decide

/-- The word of limb `k + 5 t` of prime `p` after the stores. -/
theorem read_stores (m : Mem) (B : Addr) (s : State) {p k t : Nat} (hp : p < 2) (hk : k < 5) (ht : t < 4) :
    word (wrList m B (accStores.map fun x => (x.1, s.ymm x.2))) B (D * p + 32 * k + 8 * t) =
      qw s (xr (regOf p k 0)) t := by
  rw [← qword256_ymm s _ ht, ← acc_xr p hp k hk]
  have hD : D = 3872 := rfl
  refine word_wrList_unique B ht (by rw [hD]; omega) _ m ?_ (fun x hx => ?_) (fun x hx he => ?_)
  · simp only [accStores, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_range, List.mem_map,
      Function.comp_def]
    exact ⟨p, hp, k, hk, rfl⟩
  · simp only [accStores, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_range, List.mem_map,
      Function.comp_def] at hx
    obtain ⟨p', hp', k', hk', rfl⟩ := hx
    simp only [hD]
    omega
  · simp only [accStores, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_range, List.mem_map,
      Function.comp_def] at hx
    obtain ⟨p', hp', k', hk', rfl⟩ := hx
    simp only [hD] at he ⊢
    have : p' = p ∧ k' = k := by omega
    obtain ⟨rfl, rfl⟩ := this
    rfl

/-! ## The carries -/

open VG.Impl.Rsa.X86_64.CrtIfma (at_) in
/-- Limb `j` of both primes' carry chains. -/
def limbCode (j : Nat) : List Instr :=
  [.alu .add .rdx (.mem (at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.off j))), .mov .rax (.reg .rdx),
   .alu .and .rax (.reg .r12), .store (at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.off j)) .rax, .shift .shr .rdx 52,
   .alu .add .rsi (.mem (at_ .r11 (D + VG.Impl.Rsa.X86_64.CrtIfma.off j))), .mov .rcx (.reg .rsi),
   .alu .and .rcx (.reg .r12), .store (at_ .r11 (D + VG.Impl.Rsa.X86_64.CrtIfma.off j)) .rcx,
   .shift .shr .rsi 52]

theorem carryOut_eq : carryOut = ([.mov32 .rdx (.imm 0), .mov32 .rsi (.imm 0)] : List Instr) ++ (List.range 20).flatMap limbCode := rfl

theorem and_mask {y : Nat} (hy : y < 2 ^ 64) : BitVec.ofNat 64 y &&& mask52 = BitVec.ofNat 64 (y % 2 ^ 52) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show mask52.toNat = 2 ^ 52 - 1 from rfl]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hy, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show y % 2 ^ 52 < 2 ^ 64 by omega)]

theorem off_lt (j : Nat) (hj : j < 20) : VG.Impl.Rsa.X86_64.CrtIfma.off j + 8 ≤ 160 := by
  unfold VG.Impl.Rsa.X86_64.CrtIfma.off; omega

theorem off_sep {j l : Nat} (hj : j < 20) (hl : l < 20) (h : l ≠ j) :
    VG.Impl.Rsa.X86_64.CrtIfma.off l + 8 ≤ VG.Impl.Rsa.X86_64.CrtIfma.off j ∨
      VG.Impl.Rsa.X86_64.CrtIfma.off j + 8 ≤ VG.Impl.Rsa.X86_64.CrtIfma.off l := by
  unfold VG.Impl.Rsa.X86_64.CrtIfma.off; omega

/-- `s'` is `s` with `r := v`, and maybe other flags. -/
structure Upd (s s' : State) (r : Reg) (v : BitVec 64) : Prop where
  self : s'.gpr r = v
  other : ∀ r', r' ≠ r → s'.gpr r' = s.gpr r'
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr

theorem upd_setReg (t : State) (r : Reg) (v : BitVec 64) (s : State) (hg : t.gpr = s.gpr) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hx : t.mxcsr = s.mxcsr) : Upd s (t.setReg r v) r v :=
  ⟨RegUpd.gpr_setReg_self _ _ _, fun r' h => by rw [RegUpd.gpr_setReg_of_ne _ _ h, hg], hm, hrd, hwr, hx⟩

theorem ex_add_mem {s : State} {r : Reg} {m : MemOp} (hin : InRegions (s.rd ++ s.wr) (s.ea m) 8) :
    ∃ s', exec (.alu .add r (.mem m)) s = some s' ∧ Upd s s' r (s.gpr r + s.mem.readW (s.ea m) 64) :=
  ⟨_, by simp only [exec, execAlu, readSrc, State.load64, hin, ite_true, Option.bind_some]; rfl,
    upd_setReg (arithFlags s _ _ _) _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_mov {s : State} {d r : Reg} : ∃ s', exec (.mov d (.reg r)) s = some s' ∧ Upd s s' d (s.gpr r) :=
  ⟨_, rfl, upd_setReg _ _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_and {s : State} {d r : Reg} :
    ∃ s', exec (.alu .and d (.reg r)) s = some s' ∧ Upd s s' d (s.gpr d &&& s.gpr r) :=
  ⟨_, rfl, upd_setReg _ _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_shr {s : State} {d : Reg} : ∃ s', exec (.shift .shr d 52) s = some s' ∧ Upd s s' d (s.gpr d >>> 52) :=
  ⟨_, by simp only [exec, execShift, show (1 ≤ 52 ∧ 52 ≤ 63) by decide, and_self, ite_true],
    upd_setReg (s.setFlags (some ((s.gpr d).getLsbD (52 - 1))) (if 52 = 1 then some (s.gpr d).msb else none)
      (some (s.gpr d >>> 52 == 0)) (some (s.gpr d >>> 52).msb)) _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_store {s : State} {m : MemOp} {r : Reg} (hin : InRegions s.wr (s.ea m) 8) :
    ∃ s', exec (.store m r) s = some s' ∧ s'.mem = s.mem.writeW (s.ea m) (s.gpr r) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr :=
  ⟨{ s with mem := s.mem.writeW (s.ea m) (s.gpr r) }, by simp only [exec, State.store64, hin, ite_true],
    rfl, rfl, rfl, rfl, rfl⟩

/-- After the carries of the limbs below `j`, from the stored limbs `L p`. -/
structure CarryInv (B : Addr) (L : Nat → Nat → Nat) (m₀ : Mem) (s : State) (j : Nat) : Prop where
  r11 : s.gpr .r11 = B
  r12 : s.gpr .r12 = mask52
  rdx : s.gpr .rdx = BitVec.ofNat 64 (carryIn (L 0) j)
  rsi : s.gpr .rsi = BitVec.ofNat 64 (carryIn (L 1) j)
  words : ∀ p < 2, ∀ l < 20,
    word s.mem B (D * p + VG.Impl.Rsa.X86_64.CrtIfma.off l) = BitVec.ofNat 64 (if l < j then carried (L p) l else L p l)
  frame : Outside B 0 (D + 160) m₀ s.mem

theorem ea_at {s : State} {B : Addr} (h : s.gpr .r11 = B) (d : Nat) :
    s.ea (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 d) = off B d := by
  simp only [State.ea, VG.Impl.Rsa.X86_64.CrtIfma.at_, h, off]
  exact congrArg _ (BitVec.ofInt_natCast ..)

theorem add_ofNat' {x y : Nat} (h : x + y < 2 ^ 64) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := add_ofNat h

/-- One limb of both chains. -/
theorem limb_ok {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem} {s : State} {j : Nat} (hj : j < 20)
    (hL : ∀ p < 2, ∀ l < 20, L p l < 2 ^ 61)
    (hw : ∀ d, d + 8 ≤ D + 160 → InRegions s.wr (off B d) 8)
    (h : CarryInv B L m₀ s j) :
    WP isa (.block (limbCode j)) s fun s' => CarryInv B L m₀ s' (j + 1) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : D = 3872 := rfl
  have ho := off_lt j hj
  have c0 := carryIn_lt (L := L 0) (n := j) fun l hl => hL 0 (by decide) l (by omega)
  have c1 := carryIn_lt (L := L 1) (n := j) fun l hl => hL 1 (by decide) l (by omega)
  have l0 := hL 0 (by decide) j hj
  have l1 := hL 1 (by decide) j hj
  have w0 : s.mem.readW (off B (VG.Impl.Rsa.X86_64.CrtIfma.off j)) 64 = BitVec.ofNat 64 (L 0 j) := by
    have := h.words 0 (by decide) j hj
    rw [Nat.mul_zero, Nat.zero_add, ite_eq_right_iff.2 (fun h => absurd h (by omega))] at this; exact this
  have w1 : s.mem.readW (off B (D + VG.Impl.Rsa.X86_64.CrtIfma.off j)) 64 = BitVec.ofNat 64 (L 1 j) := by
    have := h.words 1 (by decide) j hj
    rw [Nat.mul_one, ite_eq_right_iff.2 (fun h => absurd h (by omega))] at this; exact this
  have rin : ∀ d, d + 8 ≤ D + 160 → InRegions (s.rd ++ s.wr) (off B d) 8 := fun d hd => by
    obtain ⟨r, hr, hc⟩ := hw d hd; exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [limbCode, WP.block_cons_iff]
  -- p = 0
  obtain ⟨s1, e1, u1⟩ := ex_add_mem (s := s) (r := .rdx)
    (m := VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.off j))
    (by rw [ea_at h.r11]; exact rin (VG.Impl.Rsa.X86_64.CrtIfma.off j) (by omega))
  refine ⟨s1, e1, ?_⟩
  rw [ea_at h.r11, h.rdx, w0, add_ofNat' (by omega)] at u1
  rw [WP.block_cons_iff]
  obtain ⟨s2, e2, u2⟩ := ex_mov (s := s1) (d := .rax) (r := .rdx)
  refine ⟨s2, e2, ?_⟩
  rw [WP.block_cons_iff]
  obtain ⟨s3, e3, u3⟩ := ex_and (s := s2) (d := .rax) (r := .r12)
  refine ⟨s3, e3, ?_⟩
  rw [u2.self, u2.other _ (by decide), u1.self, u1.other _ (by decide), h.r12, and_mask (by omega)] at u3
  rw [WP.block_cons_iff]
  have r11₃ : s3.gpr .r11 = B := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.r11]
  obtain ⟨s4, e4, m4, g4, rd4, wr4, x4⟩ := ex_store (s := s3) (r := .rax)
    (m := VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.off j))
    (by rw [ea_at r11₃, u3.wr, u2.wr, u1.wr]; exact hw _ (by omega))
  refine ⟨s4, e4, ?_⟩
  rw [ea_at r11₃, u3.self] at m4
  rw [WP.block_cons_iff]
  obtain ⟨s5, e5, u5⟩ := ex_shr (s := s4) (d := .rdx)
  refine ⟨s5, e5, ?_⟩
  rw [congrFun g4, u3.other _ (by decide), u2.other _ (by decide), u1.self, shr_ofNat (by omega)] at u5
  -- p = 1
  have r11₅ : s5.gpr .r11 = B := by rw [u5.other _ (by decide), congrFun g4, r11₃]
  have mem₅ : s5.mem = (s.mem.writeW (off B (VG.Impl.Rsa.X86_64.CrtIfma.off j))
      (BitVec.ofNat 64 ((carryIn (L 0) j + L 0 j) % 2 ^ 52))) := by
    rw [u5.mem, m4, u3.mem, u2.mem, u1.mem]
  have w1' : s5.mem.readW (off B (D + VG.Impl.Rsa.X86_64.CrtIfma.off j)) 64 = BitVec.ofNat 64 (L 1 j) := by
    rw [mem₅]
    exact ((writeW_outside s.mem B _ (by omega)).word (by omega) (by omega)).trans w1
  have wr₅ : s5.wr = s.wr := by rw [u5.wr, wr4, u3.wr, u2.wr, u1.wr]
  have rd₅ : s5.rd = s.rd := by rw [u5.rd, rd4, u3.rd, u2.rd, u1.rd]
  rw [WP.block_cons_iff]
  obtain ⟨s6, e6, u6⟩ := ex_add_mem (s := s5) (r := .rsi)
    (m := VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (D + VG.Impl.Rsa.X86_64.CrtIfma.off j))
    (by rw [ea_at r11₅, rd₅, wr₅]; exact rin _ (by omega))
  refine ⟨s6, e6, ?_⟩
  have rsi₅ : s5.gpr .rsi = BitVec.ofNat 64 (carryIn (L 1) j) := by
    rw [u5.other _ (by decide), congrFun g4, u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), h.rsi]
  rw [ea_at r11₅, rsi₅, w1', add_ofNat' (by omega)] at u6
  rw [WP.block_cons_iff]
  obtain ⟨s7, e7, u7⟩ := ex_mov (s := s6) (d := .rcx) (r := .rsi)
  refine ⟨s7, e7, ?_⟩
  rw [WP.block_cons_iff]
  obtain ⟨s8, e8, u8⟩ := ex_and (s := s7) (d := .rcx) (r := .r12)
  refine ⟨s8, e8, ?_⟩
  have r12₇ : s7.gpr .r12 = mask52 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), congrFun g4,
      u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.r12]
  rw [u7.self, u6.self, r12₇, and_mask (by omega)] at u8
  have r11₈ : s8.gpr .r11 = B := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), r11₅]
  rw [WP.block_cons_iff]
  obtain ⟨s9, e9, m9, g9, rd9, wr9, x9⟩ := ex_store (s := s8) (r := .rcx)
    (m := VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (D + VG.Impl.Rsa.X86_64.CrtIfma.off j))
    (by rw [ea_at r11₈, u8.wr, u7.wr, u6.wr, wr₅]; exact hw _ (by omega))
  refine ⟨s9, e9, ?_⟩
  rw [ea_at r11₈, u8.self] at m9
  rw [WP.block_cons_iff]
  obtain ⟨s10, e10, u10⟩ := ex_shr (s := s9) (d := .rsi)
  refine ⟨s10, e10, ?_⟩
  rw [congrFun g9, u8.other _ (by decide), u7.other _ (by decide), u6.self, shr_ofNat (by omega)] at u10
  refine WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [u10.other _ (by decide), congrFun g9, r11₈]
  · rw [u10.other _ (by decide), congrFun g9, u8.other _ (by decide), r12₇]
  · rw [u10.other _ (by decide), congrFun g9, u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.self]
    simp only [carryIn]; rw [Nat.add_comm]
  · rw [u10.self]; simp only [carryIn]; rw [Nat.add_comm]
  · have mem₁₀ : s10.mem = (s5.mem.writeW (off B (D + VG.Impl.Rsa.X86_64.CrtIfma.off j))
        (BitVec.ofNat 64 ((carryIn (L 1) j + L 1 j) % 2 ^ 52))) := by
      rw [u10.mem, m9, u8.mem, u7.mem, u6.mem]
    intro p hp l hl
    have hol := off_lt l hl
    rw [mem₁₀, mem₅]
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
    · rw [Nat.mul_zero, Nat.zero_add, (writeW_outside _ B _ (by omega)).word (by omega) (by omega)]
      by_cases hlj : l = j
      · subst hlj
        rw [word_writeW_self]
        simp only [carried, show l < l + 1 by omega, ite_true]; rw [Nat.add_comm]
      · have hs := off_sep hj hl hlj
        rw [(writeW_outside _ B _ (by omega)).word (by omega) (by omega)]
        have := h.words 0 (by decide) l hl
        rw [Nat.mul_zero, Nat.zero_add] at this
        rw [this]
        by_cases hlt : l < j
        · simp only [hlt, show l < j + 1 by omega, ite_true]
        · simp only [hlt, show ¬ l < j + 1 by omega, ite_false]
    · rw [Nat.mul_one]
      by_cases hlj : l = j
      · subst hlj
        rw [word_writeW_self]
        simp only [carried, show l < l + 1 by omega, ite_true]; rw [Nat.add_comm]
      · have hs := off_sep hj hl hlj
        rw [(writeW_outside _ B _ (by omega)).word (by omega) (by omega),
          (writeW_outside _ B _ (by omega)).word (by omega) (by omega)]
        have := h.words 1 (by decide) l hl
        rw [Nat.mul_one] at this
        rw [this]
        by_cases hlt : l < j
        · simp only [hlt, show l < j + 1 by omega, ite_true]
        · simp only [hlt, show ¬ l < j + 1 by omega, ite_false]
  · rw [u10.mem, m9, u8.mem, u7.mem, u6.mem, mem₅]
    exact (h.frame.trans ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega))).trans
      ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega))
  · intro r h1 h2 h3 h4
    rw [u10.other _ h4, congrFun g9, u8.other _ h2, u7.other _ h2, u6.other _ h4, u5.other _ h3, congrFun g4,
      u3.other _ h1, u2.other _ h1, u1.other _ h3]
  · rw [u10.rd, rd9, u8.rd, u7.rd, u6.rd, rd₅]
  · rw [u10.wr, wr9, u8.wr, u7.wr, u6.wr, wr₅]
  · rw [u10.mxcsr, x9, u8.mxcsr, u7.mxcsr, u6.mxcsr, u5.mxcsr, x4, u3.mxcsr, u2.mxcsr, u1.mxcsr]


/-- The limbs from `j` on. -/
theorem limbs_ok {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem}
    (hL : ∀ p < 2, ∀ l < 20, L p l < 2 ^ 61) :
    ∀ n j (s : State), j + n = 20 → (∀ d, d + 8 ≤ D + 160 → InRegions s.wr (off B d) 8) →
      CarryInv B L m₀ s j →
      WP isa (.block ((List.range' j n).flatMap limbCode)) s fun s' => CarryInv B L m₀ s' 20 ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr
  | 0, j, s, hn, _, h => WP.block_nil ⟨by rw [← hn]; exact h, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, j, s, hn, hw, h => by
    rw [List.range'_succ, List.flatMap_cons]
    refine WP.block_append (WP.mono (limb_ok (by omega) hL hw h) fun s₁ ⟨h₁, g₁, rd₁, wr₁, x₁⟩ =>
      WP.mono (limbs_ok hL n (j + 1) s₁ (by omega) (fun d hd => wr₁ ▸ hw d hd) h₁)
        fun s₂ ⟨h₂, g₂, rd₂, wr₂, x₂⟩ => ⟨h₂, fun r a b c d => (g₂ r a b c d).trans (g₁ r a b c d),
          rd₂.trans rd₁, wr₂.trans wr₁, x₂.trans x₁⟩)

/-- The carry pass, from the limbs `L p` stored. -/
theorem carryOut_ok {B : Addr} {L : Nat → Nat → Nat} {s : State}
    (hL : ∀ p < 2, ∀ l < 20, L p l < 2 ^ 61) (hw : ∀ d, d + 8 ≤ D + 160 → InRegions s.wr (off B d) 8)
    (hr11 : s.gpr .r11 = B) (hr12 : s.gpr .r12 = mask52)
    (hwords : ∀ p < 2, ∀ l < 20, word s.mem B (D * p + VG.Impl.Rsa.X86_64.CrtIfma.off l) = BitVec.ofNat 64 (L p l)) :
    WP isa (.block carryOut) s fun s' => CarryInv B L s.mem s' 20 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have g2 : ∀ r, r ≠ .rdx → r ≠ .rsi → ((s.setReg .rdx 0).setReg .rsi 0).gpr r = s.gpr r :=
    fun r a b => by rw [RegUpd.gpr_setReg_of_ne _ _ b, RegUpd.gpr_setReg_of_ne _ _ a]
  rw [carryOut_eq, List.cons_append, WP.block_cons_iff]
  refine ⟨s.setReg .rdx 0, rfl, ?_⟩
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨(s.setReg .rdx 0).setReg .rsi 0, rfl, ?_⟩
  rw [List.nil_append, List.range_eq_range']
  refine WP.mono (limbs_ok hL 20 0 _ rfl hw ⟨by rw [g2 _ (by decide) (by decide), hr11],
    by rw [g2 _ (by decide) (by decide), hr12], ?_, by rw [RegUpd.gpr_setReg_self]; rfl,
    fun p hp l hl => hwords p hp l hl, fun _ _ => rfl⟩) fun s' ⟨h, g, rd, wr, x⟩ =>
    ⟨h, fun r a b c d => (g r a b c d).trans (g2 r c d), rd, wr, x⟩
  rfl


/-! ## The whole multiplication -/

/-- Writes of 32 bytes below `n` leave the rest. -/
theorem wrList_outside (B : Addr) {n : Nat} (hn : n ≤ 2 ^ 63) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (∀ x ∈ l, x.1 + 32 ≤ n) → Outside B 0 n m (wrList m B l)
  | [], m, _ => Outside.refl B 0 n m
  | (e, v) :: rest, m, h => by
    have he := h (e, v) (List.mem_cons_self ..)
    exact ((writeW256_outside m B v (by omega)).mono (by omega) (by omega)).trans
      (wrList_outside B hn rest _ fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem accStores_lt : ∀ x ∈ accStores, x.1 + 32 ≤ D + 160 := by decide

/-- `ammCore` from the operands `a` (at `r8`), `b` (at `r9`) and the modulus `m`
with `k` (at `rbx`), into limbs at `r11 = B`: each prime's limbs carried, and
its carry out. -/
theorem ammCore_ok {s : State} {B : Addr} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    (e : Env (s.setReg .r10 (s.gpr .rbx)) a m k bl) (hB : s.gpr .r11 = B) (hs : Scr s B (D + 160)) :
    WP isa VG.Impl.Rsa.X86_64.CrtIfma.ammCore s fun s' =>
      (∀ p < 2, ∀ l < 20, word s'.mem B (D * p + VG.Impl.Rsa.X86_64.CrtIfma.off l) =
        BitVec.ofNat 64 (carried (lm a m k bl p 20) l)) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (carryIn (lm a m k bl 0 20) 20) ∧
      s'.gpr .rsi = BitVec.ofNat 64 (carryIn (lm a m k bl 1 20) 20) ∧
      Outside B 0 (D + 160) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : D = 3872 := rfl
  refine WP.seq ?_
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨s.setReg .r10 (s.gpr .rbx), rfl, ?_⟩
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  refine WP.mono (zeros_ok (s := (s.setReg .r10 (s.gpr .rbx)).setReg32 .rcx 4)) fun s₁ ⟨hz, k₁⟩ => ?_
  have g₁ : ∀ r, r ≠ .rax → r ≠ .rcx → s₁.gpr r = (s.setReg .r10 (s.gpr .rbx)).gpr r := fun r a c => by
    rw [k₁.gpr r a]; exact RegUpd.gpr_setReg_of_ne _ _ c
  have i₁ : InBlk (s.setReg .r10 (s.gpr .rbx)) s₁ a m k bl 0 0 :=
    ⟨fun p hp kk hk t ht => by
      rw [hz _ (by unfold regOf; omega) t ht]; rfl,
     fun t ht => hz 14 (by decide) t ht, g₁ _ (by decide) (by decide),
     by rw [g₁ _ (by decide) (by decide), Nat.mul_zero, BitVec.add_zero], g₁ _ (by decide) (by decide),
     k₁.mem, k₁.rd, k₁.wr⟩
  refine WP.seq (WP.mono (loop_ok e 4 s₁ (by decide) (by decide) i₁ (by rw [k₁.gpr _ (by decide)]; rfl))
    fun s₂ ⟨i₂, g₂, x₂⟩ => ?_)
  have hB₂ : s₂.gpr .r11 = B := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
    exact (RegUpd.gpr_setReg_of_ne _ _ (by decide)).trans hB
  have wr₂ : s₂.wr = s.wr := by rw [i₂.wr]; rfl
  rw [accStores_code, List.append_assoc, WP.block_append_iff]
  refine WP.mono (stores_gen accStores s₂ hB₂ fun x hx =>
    wr₂ ▸ (let ⟨_, h, c⟩ := hs.region (accStores_lt x hx) (by decide); ⟨_, h, c⟩)) fun s₃ h₃ => ?_
  subst h₃
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  have m₂ : s₂.mem = s.mem := i₂.mem
  refine WP.mono (carryOut_ok (B := B) (L := fun p => lm a m k bl p 20) (fun p _ l hl => lm_lt (by decide) hl)
    (fun d hd => by rw [RegUpd.wr_setReg, wr₂]; exact hs.st hd) (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB₂)
    (RegUpd.gpr_setReg_self _ _ _) fun p hp l hl => ?_) fun s' ⟨h, g, rd, wr, x⟩ => ?_
  · have := read_stores s₂.mem B s₂ hp (k := l % 5) (t := l / 5) (Nat.mod_lt _ (by decide)) (by omega)
    rw [i₂.lanes p hp _ (Nat.mod_lt _ (by decide)) _ (by omega), Nat.mod_add_div] at this
    rw [RegUpd.mem_setReg, show D * p + VG.Impl.Rsa.X86_64.CrtIfma.off l = D * p + 32 * (l % 5) + 8 * (l / 5) by
      unfold VG.Impl.Rsa.X86_64.CrtIfma.off; omega]
    exact this
  refine ⟨fun p hp l hl => by rw [h.words p hp l hl]; simp only [hl, ite_true], h.rdx, h.rsi, ?_, fun r r1 r2 r3 r4 r5 r6 r7 => ?_,
    by rw [rd, RegUpd.rd_setReg, i₂.rd]; rfl, by rw [wr, RegUpd.wr_setReg, wr₂],
    by rw [x, RegUpd.mxcsr_setReg, x₂, k₁.mxcsr]; rfl⟩
  · have o := wrList_outside B (n := D + 160) (by omega) (accStores.map fun x => (x.1, s₂.ymm x.2)) s₂.mem
      fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact accStores_lt y hy
    have hf : Outside B 0 (D + 160) (wrList s₂.mem B (accStores.map fun x => (x.1, s₂.ymm x.2))) s'.mem := h.frame
    have o' : Outside B 0 (D + 160) s.mem (wrList s₂.mem B (accStores.map fun x => (x.1, s₂.ymm x.2))) :=
      fun x hx => (o x hx).trans (congrFun m₂ x)
    exact o'.trans hf
  · rw [g r r1 r2 r3 r4, RegUpd.gpr_setReg_of_ne _ _ r7, g₂ r r1 r2 r5, g₁ r r1 r2, RegUpd.gpr_setReg_of_ne _ _ r6]

end VG.Proof.Bignum.X86_64.AmmSym
