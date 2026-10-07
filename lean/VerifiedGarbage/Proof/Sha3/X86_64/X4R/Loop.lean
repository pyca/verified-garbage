import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Round

/-!
# Keccak-f[1600] four times at once, in registers: the permutation

`permute4R` loads the four interleaved states at `rdi` into the registers
(`load_ok`), runs the 24 rounds on them (`round_ok`, one per iteration of
its loop), and stores them back (`store_ok`): Keccak-f[1600] on each of the
four states (`permute4R_ok`), with the interface of `X4.permute4_ok`.
-/

namespace VG.Proof.Sha3.X86_64.X4R

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4R
open VG.Spec.Sha3 (keccakF rnd RC)
open VG.Proof.Sha3 (outState outState_eq foldl_succ out)
open VG.Proof.Sha3.X86_64.X4 (KState Lane la la_eq Lanes4 Pre4 end_beq la_contains la_rc)
open VG.Proof.Sha3.X86_64 (wp_nil ea_at)
open VG.Impl.Sha3.X86_64 (at_)

/-! ## A round -/

theorem out_zero (A : KState) (rc : Lane) : out A rc 0 0 = out A 0 0 0 ^^^ rc := by
  simp [out]

theorem outState_get (A : KState) (rc : Lane) {i : Nat} (hi : i < 25) :
    (outState A rc)[i]! = out A rc (i % 5) (i / 5) := by
  simp [outState, hi]

theorem round_ok (s : State) (A : Nat → KState) (rcp : Addr) (rc : Lane) (hA : Regs4 s A)
    (hrdx : s.gpr .rdx = rcp) (hin : InRegions (s.rd ++ s.wr) rcp 32)
    (hrc : ∀ k < 4, s.mem.readW (la rcp 0 k) 64 = rc) :
    WP isa (.block round) s fun s' =>
      Regs4 s' (fun k => outState (A k) rc) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rdx = rcp + 32 ∧ (∀ g, g ≠ .rdx → s'.gpr g = s.gpr g) ∧
      s'.zf = some (rcp + 32 - s.gpr .rcx == 0) := by
  unfold round
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (columns_ok s A hA) fun s₁ ⟨k₁, r₁, c₁⟩ => ?_
  refine WP.mono (dcols_ok s₁ A r₁ c₁) fun s₂ ⟨k₂, _, d₂⟩ => ?_
  refine WP.mono (rhoPi_ok s₂ A fun i hi k hk => by rw [d₂ i hi k hk, ite_t (show i % 5 < 5 by omega)])
    fun s₃ ⟨k₃, _, b₃⟩ => ?_
  refine WP.mono (chis_ok s₃ A b₃) fun s₄ ⟨k₄, x₄⟩ => ?_
  have k := ((k₁.trans k₂).trans k₃).trans k₄
  refine WP.mono (iota_ok s₄ rcp rc (by rw [k.gpr, hrdx]) (by rw [k.rd, k.wr]; exact hin)
    (by rw [k.mem]; exact hrc)) fun s₅ ⟨m₅, r₅, w₅, z₅, o₅, d₅, g₅, f₅⟩ => ?_
  refine ⟨fun i hi j hj => ?_, by rw [m₅, k.mem], by rw [r₅, k.rd], by rw [w₅, k.wr], d₅,
    fun g hg => by rw [g₅ g hg, k.gpr], by rw [f₅, k.gpr]⟩
  rw [outState_get _ _ hi]
  by_cases e : i = 0
  · subst e
    rw [z₅ j hj, x₄ 0 hi j hj, ite_t (show 0 / 5 < 5 by decide), out_zero]; rfl
  · rw [o₅ i hi e j hj, x₄ i hi j hj, ite_t (show i / 5 < 5 by omega), Xp,
      Proof.Sha3.X86_64.X4R.out_t _ rc _ _ (by omega)]

/-! ## Loading and storing the states -/

/-- After loading the first `n` lanes. -/
def LdInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ ∀ i < n, ∀ k < 4, qy s (lreg i) k = (A k)[i]!

theorem load_ok (s₀ : State) (src : Addr) (A : Nat → KState) (hdi : s₀.gpr .rdi = src)
    (hin : ∀ i < 25, InRegions s₀.wr (src + BitVec.ofNat 64 (32 * i)) 32) (hA : Lanes4 s₀.mem src A) :
    WP isa (.block load) s₀ fun s => Same s₀ s ∧ Regs4 s A := by
  refine WP.mono (wp_range_map (LdInv s₀ A) (fun i s hi ⟨hw, hl⟩ => ?_) s₀
    ⟨Same.refl _, fun _ h => absurd h (by omega)⟩) fun s h => h
  refine wp_evld (by rw [ea_at, hw.gpr, hdi]) (by rw [hw.rd, hw.wr]; exact X4.in_append (hin i hi))
    fun s' u => wp_nil ⟨hw.trans u.same, fun j hj k hk => ?_⟩
  by_cases e : j = i
  · subst e; rw [u.val k hk, la_eq, hw.mem, hA j hi k hk]
  · rw [u.other _ (lreg_ne (by omega) hi e) k hk, hl j (by omega) k hk]

/-- After storing the first `n` lanes. -/
def StInv (s₀ : State) (src : Addr) (n : Nat) (s : State) : Prop :=
  s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ (∀ r k, qy s r k = qy s₀ r k) ∧
    Frame [⟨src, 800⟩] s₀.mem s.mem ∧ ∀ i < n, ∀ k < 4, s.mem.readW (la src i k) 64 = qy s₀ (lreg i) k

theorem store_ok (s₀ : State) (src : Addr) (hdi : s₀.gpr .rdi = src)
    (hin : ∀ i < 25, InRegions s₀.wr (src + BitVec.ofNat 64 (32 * i)) 32) :
    WP isa (.block store) s₀ (StInv s₀ src 25) := by
  refine wp_range_map (StInv s₀ src) (fun i s hi ⟨hg, hrd, hwr, hq, hf, hl⟩ => ?_) s₀
    ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  refine wp_evst (by rw [ea_at, hg, hdi]) (by rw [hwr]; exact hin i hi) (wp_nil ⟨hg, hrd, hwr, hq, ?_, ?_⟩)
  · exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base src (by omega) (by omega))
  · intro j hj k hk
    by_cases e : j = i
    · subst e
      show (s.mem.writeW _ _).readW _ 64 = _
      rw [← la_eq, readW_evst _ _ _ _ hk, hq]
    · show (s.mem.writeW _ _).readW _ 64 = _
      have := readW_writeW_off s.mem src (s.vy (lreg i)) (d := 32 * j + 8 * k) (e := 32 * i) (n := 8)
        (by omega) (by omega) (by omega)
      rw [this]
      exact hl j (by omega) k hk

/-! ## The 24 rounds -/

/-- Before round `r`. -/
structure RInv (s₀ : State) (tbl : Addr) (A : Nat → KState) (r : Nat) (s : State) : Prop where
  regs : Regs4 s fun k => (List.range r).foldl rnd (A k)
  rdx : s.gpr .rdx = tbl + BitVec.ofNat 64 (32 * r)
  rest : ∀ g, g ≠ .rdx → s.gpr g = s₀.gpr g
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem round_step {s₀ : State} {src oth tbl : Addr} {A : Nat → KState} (hp : Pre4 s₀ src oth tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {r : Nat} (hr : r < 24) {s : State}
    (h : RInv s₀ tbl A r s) :
    WP isa (.block round) s fun s' => eval .ne s' = some (!decide (r + 1 = 24)) ∧ RInv s₀ tbl A (r + 1) s' := by
  refine WP.mono (round_ok s _ _ (RC r) h.regs h.rdx (by rw [h.rd, h.wr]; exact hp.tbl_in r hr)
    fun k hk => by rw [la_rc, h.mem]; exact hp.rc r hr k hk) fun s' ⟨hg, hm, hrd, hwr, hdx, ho, hz⟩ => ?_
  have hcx' : s.gpr .rcx = tbl + BitVec.ofNat 64 768 := by rw [h.rest _ (by decide), hcx]
  refine ⟨?_, ⟨fun i hi k hk => ?_, ?_, fun g hg' => by rw [ho g hg', h.rest g hg'], hm.trans h.mem,
    hrd.trans h.rd, hwr.trans h.wr⟩⟩
  · simp only [eval, hz, hcx', Option.map_some, end_beq tbl r hr]
  · rw [hg i hi k hk]; simp only [foldl_succ, ← outState_eq]
  · rw [hdx, BitVec.add_assoc, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]; rfl

/-- The 24 rounds on each of the four states at `src` (with the table of
`X4.permute4`, and its interface): Keccak-f[1600] on each, with `rdx` at the
end of the table and every other register as it was. -/
theorem permute4R_ok {s₀ : State} {src oth tbl : Addr} (hp : Pre4 s₀ src oth tbl)
    (hdi : s₀.gpr .rdi = src) (hdx : s₀.gpr .rdx = tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {A : Nat → KState} (hA : Lanes4 s₀.mem src A) :
    WP isa permute4R s₀ fun s =>
      Lanes4 s.mem src (fun k => keccakF (A k)) ∧ Frame [⟨src, 800⟩, ⟨oth, 800⟩] s₀.mem s.mem ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.gpr .rdx = tbl + BitVec.ofNat 64 768 ∧
      ∀ g, g ≠ .rax → g ≠ .rdx → s.gpr g = s₀.gpr g := by
  unfold permute4R
  refine WP.seq (WP.mono (load_ok s₀ src A hdi hp.src_in hA) fun s₁ ⟨k₁, r₁⟩ => ?_)
  have h₀ : RInv s₀ tbl A 0 s₁ := ⟨by simpa using r₁, by rw [k₁.gpr, hdx]; exact (BitVec.add_zero _).symm,
    fun g _ => by rw [k₁.gpr], k₁.mem, k₁.rd, k₁.wr⟩
  let Inv : Nat → State → Prop := fun n s => ∃ r, n = 24 - r ∧ r < 24 ∧ RInv s₀ tbl A r s
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := RInv s₀ tbl A 24) Inv (fun n s ⟨r, hn, hr, h⟩ => ?_)
    24 s₁ ⟨0, rfl, by omega, h₀⟩) fun s₂ h₂ => ?_)
  · refine WP.mono (round_step hp hcx hr h) fun s' ⟨he, h'⟩ => ?_
    by_cases hlast : r + 1 = 24
    · exact .inl ⟨by show eval .ne s' = _; rw [he, hlast]; rfl, hlast ▸ h'⟩
    · exact .inr ⟨by show eval .ne s' = _; rw [he]; simp [hlast], 24 - (r + 1), by omega, r + 1, rfl, by omega, h'⟩
  · refine WP.mono (store_ok s₂ src (by rw [h₂.rest _ (by decide), hdi]) (by rw [h₂.wr]; exact hp.src_in))
      fun s ⟨hg, hrd, hwr, _, hf, hl⟩ => ⟨fun i hi k hk => by rw [hl i hi k hk, h₂.regs i hi k hk]; rfl,
        ?_, hrd.trans h₂.rd, hwr.trans h₂.wr, by rw [hg, h₂.rdx], fun g _ hd => by rw [hg, h₂.rest g hd]⟩
    rw [← h₂.mem]
    refine hf.sub fun R hR => ?_
    simp only [List.mem_singleton] at hR; subst hR
    exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.Sha3.X86_64.X4R

namespace VG.Proof.Sha3.X86_64.X4

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4
open VG.Spec.Sha3 (keccakF)

/-- `permute4` (`permute4M`, or with `fast` `X4R.permute4R`): Keccak-f[1600]
on each of the four states at `src`, with `rdi`, `rsi` and every register but
`rax` and `rdx` as they were. -/
theorem permute4_ok {s₀ : State} {src oth tbl : Addr} (hp : Pre4 s₀ src oth tbl)
    (hdi : s₀.gpr .rdi = src) (hsi : s₀.gpr .rsi = oth) (hdx : s₀.gpr .rdx = tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {A : Nat → KState} (hA : Lanes4 s₀.mem src A)
    (fast : Bool := false) :
    WP isa (permute4 fast) s₀ fun s =>
      Lanes4 s.mem src (fun k => keccakF (A k)) ∧ Frame [⟨src, 800⟩, ⟨oth, 800⟩] s₀.mem s.mem ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.gpr .rdx = tbl + BitVec.ofNat 64 768 ∧
      ∀ g, g ≠ .rax → g ≠ .rdx → s.gpr g = s₀.gpr g := by
  cases fast
  · exact permute4M_ok hp hdi hsi hdx hcx hA
  · exact X4R.permute4R_ok hp hdi hdx hcx hA

end VG.Proof.Sha3.X86_64.X4
