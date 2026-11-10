module

public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Stage
public import VerifiedGarbage.Proof.X25519.X86_64.Small
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Block
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Carry
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X25519 on x86-64 with AVX512_IFMA: the blocks of an iteration

Each block of `vstep` as a fact about states: the limbs it leaves in registers
and slots (`lanes`, `slotv`), as numbers, from those it starts with, and what
it keeps.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw sel4)

theorem xi_xr : ∀ r < 16, xi (xr r) = r := by decide

/-- Limb `i` of lane `l` of the registers from `r` up. -/
def lanes (s : State) (r l i : Nat) : Nat := (qw s (xr (r + i)) l).toNat

/-- Limb `i` of lane `l` of the slot at `d`. -/
def slotv (m : Mem) (base : Addr) (d l i : Nat) : Nat := (mq m base (d + 32 * i + 8 * l)).toNat

/-- The quadword of `vpermd`'s indices of the doublewords of lane `q`. -/
def kq (q : Nat) : BitVec 64 := BitVec.ofNat 64 (2 * q + (2 * q + 1) * 2 ^ 32)
/-- The quadwords of `vidx`'s indices: `KIU`'s, of the lanes `(0, 1, 3, 2)`,
and `KIV`'s, of the lanes `(0, 1, 0, 1)`. -/
def kiu (l : Nat) : BitVec 64 := kq (if l < 2 then l else 5 - l)
def kiv (l : Nat) : BitVec 64 := kq (l % 2)

/-- The constants of the working space, with `x₁`'s limbs. -/
structure Consts (m : Mem) (base : Addr) (x1 : Nat → Nat) : Prop where
  km : ∀ l < 4, (mq m base (KM + 8 * l)).toNat = 2 ^ 51 - 1
  k19 : ∀ l < 4, (mq m base (K19 + 8 * l)).toNat = 19
  kb0 : ∀ l < 4, (mq m base (KB0 + 8 * l)).toNat = 2 ^ 62 - 38912
  kb1 : ∀ l < 4, (mq m base (KB1 + 8 * l)).toNat = 2 ^ 62 - 2048
  a24 : ∀ i < 5, ∀ l < 4, slotv m base KA24 l i = if i = 0 ∧ l = 1 then 121665 else 0
  kx1 : ∀ i < 5, ∀ l < 4, slotv m base KX1 l i = if l = 3 then x1 i else if i = 0 ∧ l ≠ 1 then 1 else 0
  x1 : ∀ i < 5, x1 i < 2 ^ 52
  k13 : ∀ l < 4, (mq m base (K13 + 8 * l)).toNat = 2 ^ 13 - 1
  k26 : ∀ l < 4, (mq m base (K26 + 8 * l)).toNat = 2 ^ 26 - 1
  k39 : ∀ l < 4, (mq m base (K39 + 8 * l)).toNat = 2 ^ 39 - 1
  k4d : ∀ l < 4, mq m base (K4D + 8 * l) = 0x0000000400000004
  kiu : ∀ l < 4, mq m base (KIU + 8 * l) = kiu l
  kiv : ∀ l < 4, mq m base (KIV + 8 * l) = kiv l

/-- The constants the carries and the differences read. -/
structure CConsts (m : Mem) (base : Addr) : Prop where
  km : ∀ l < 4, (mq m base (KM + 8 * l)).toNat = 2 ^ 51 - 1
  k19 : ∀ l < 4, (mq m base (K19 + 8 * l)).toNat = 19
  kb0 : ∀ l < 4, (mq m base (KB0 + 8 * l)).toNat = 2 ^ 62 - 38912
  kb1 : ∀ l < 4, (mq m base (KB1 + 8 * l)).toNat = 2 ^ 62 - 2048

theorem Consts.c {m : Mem} {base : Addr} {x1 : Nat → Nat} (hk : Consts m base x1) : CConsts m base :=
  ⟨hk.km, hk.k19, hk.kb0, hk.kb1⟩

theorem envOf_m {s : State} {base : Addr} (hs : s.gpr .rdi = base) (d l : Nat) :
    (envOf s).m d l = (mq s.mem base (d + 8 * l)).toNat := by
  simp only [envOf, mq, hs]

theorem envOf_v (s : State) (r l : Nat) : (envOf s).v r l = (qw s (xr r) l).toNat := rfl

/-- The environment's bounds, from the registers and memory. -/
theorem envOK_of {s : State} {base : Addr} (hs : s.gpr .rdi = base) {B : Bnds}
    (hv : ∀ r l, l < 4 → (qw s (xr r) l).toNat ≤ B.v r) (hg : ∀ g, B.g g = 2 ^ 64 - 1)
    (hm : ∀ d l, l < 4 → (mq s.mem base (d + 8 * l)).toNat ≤ B.m d)
    (hml : ∀ d l, l < 4 → B.ml d ≤ (mq s.mem base (d + 8 * l)).toNat)
    (hh : ∀ r l, l < 4 → (qwH s (hr r) l).toNat ≤ B.h r := by intros; exact Nat.le_sub_one_of_lt (BitVec.isLt _)) :
    EnvOK s B :=
  ⟨hv, fun g => by rw [hg]; exact Nat.le_sub_one_of_lt (BitVec.isLt _),
    fun d k hk => by have := hm d k hk; simpa only [mq, hs] using this,
    fun d k hk => by have := hml d k hk; simpa only [mq, hs] using this, hh⟩

theorem lt64 (x : BitVec 64) : x.toNat ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt x.isLt

/-- What a block run symbolically leaves in a register. -/
theorem SRel.out {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {B : Bnds} (hE : EnvOK s₀ B) {r l : Nat}
    (hr : r < 16) (hl : l < 4) (ho : (σ.reg r).ok B l = true) :
    (qw s (xr r) l).toNat = (σ.reg r).nat (envOf s₀) l ∧ (qw s (xr r) l).toNat ≤ (σ.reg r).bnd B l := by
  have := h.nat hE (r := xr r) hl (by rw [xi_xr r hr]; exact ho)
  rwa [xi_xr r hr] at this

theorem SRel.keep {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {r l : Nat} (hr : r < 16) (hl : l < 4)
    (hk : σ.reg r = .reg r) : qw s (xr r) l = qw s₀ (xr r) l := by
  rw [h.reg _ l hl, xi_xr r hr, hk]; rfl

/-- Limb `i` of lane `l` of `ymm (16 + i)`, as a number. -/
def hlanes (s : State) (l i : Nat) : Nat := (qwH s (hr i) l).toNat

theorem hidx_hr : ∀ r < 16, hidx (hr r) = r := by decide

/-- The term a block run symbolically leaves in `ymm (16 + r)`. -/
theorem SRel.hterm {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {r l : Nat} (hr16 : r < 16) (hl : l < 4) :
    qwH s (hr r) l = (σ.hreg r).eval s₀ l := by
  rw [h.hreg _ l hl, hidx_hr r hr16]

/-! ## Carries -/

theorem kx1_le {m : Mem} {base : Addr} {x1 : Nat → Nat} (hk : Consts m base x1) {i l : Nat} (hi : i < 5)
    (hl : l < 4) : slotv m base KX1 l i < 2 ^ 52 := by
  rw [hk.kx1 i hi l hl]; have := hk.x1 i hi; split <;> [omega_arith; split <;> omega_arith]

/-- What `carry r` leaves: limbs `r0` to `r0 + 4` carried. -/
def CarryPost (r0 : Nat) (s s' : State) : Prop :=
  vm s s' = s' ∧ s'.mem = s.mem ∧
    (∀ l < 4, ∀ i < 5, lanes s' r0 l i = carryNat (2 ^ 51 - 1) 19 (lanes s r0 l) i ∧
      lanes s' r0 l i < 2 ^ 52) ∧
    (∀ r < 16, ¬ (r0 ≤ r ∧ r < r0 + 5) → ¬ (10 ≤ r ∧ r < 13) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)

theorem carry_env {r : Nat → Nat} {r0 : Nat} (hr : ∀ i, r i = r0 + i) {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s r0 l i < 2 ^ 63) : EnvOK s (carryB r) := by
  refine envOK_of hs (fun r' l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
  · simp only [carryB, hr]
    split
    · rename_i h
      have : ∃ i < 5, r' = r0 + i := by rcases h with h | h | h | h | h <;> exact ⟨_, by omega_arith, h⟩
      obtain ⟨i, hi, rfl⟩ := this
      exact Nat.le_sub_one_of_lt (hx l hl i hi)
    · exact lt64 _
  · simp only [carryB]
    split
    · subst_vars; rw [hk.km l hl]
    · split
      · subst_vars; rw [hk.k19 l hl]
      · exact lt64 _

theorem carryI_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : Ctx s) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 63) :
    WP isa (.block (carry id)) s (CarryPost 0 s) := by
  have hE := carry_env (r := id) (fun i => (Nat.zero_add i).symm) hs hk hx
  have e : Sym.init.run (carry id) = some carryI := carryS_eq id _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, carryI_st]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => ?_⟩
  · obtain ⟨o, b⟩ := carryI_ok i hi l hl
    obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
    have hs' : (fun j => lanes s 0 l j) = fun j => (envOf s).v j l := by
      funext j; simp only [lanes, Nat.zero_add, envOf_v]
    refine ⟨?_, by simp only [lanes, Nat.zero_add]; omega_arith⟩
    simp only [lanes, Nat.zero_add] at e ⊢
    rw [e, carryI_nat _ _ i hi, envOf_m hs, envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']
  · exact h.keep hr hl (carryI_keep r hr (by omega_arith))

theorem carryF_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : Ctx s) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 63) :
    WP isa (.block (carry (5 + ·))) s (CarryPost 5 s) := by
  have hE := carry_env (r := (5 + ·)) (fun i => rfl) hs hk hx
  have e : Sym.init.run (carry (5 + ·)) = some carryF := carryS_eq (5 + ·) _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, carryF_st]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => ?_⟩
  · obtain ⟨o, b⟩ := carryF_ok i hi l hl
    obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
    have hs' : (fun j => lanes s 5 l j) = fun j => (envOf s).v (5 + j) l := by
      funext j; simp only [lanes, envOf_v]
    refine ⟨?_, by simp only [lanes]; omega_arith⟩
    simp only [lanes] at e ⊢
    rw [e, carryF_nat _ _ i hi, envOf_m hs, envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']
  · exact h.keep hr hl (carryF_keep r hr (by omega_arith))

/-! ## Memory -/

open VG.Proof.X25519.X86_64 (Outside ofs word off) in
/-- Stores to slots in `[o, o + n)` change nothing outside it. -/
theorem stores_outside (s₀ : State) (base : Addr) (m : Mem) {o n : Nat} (hn : o + n < 2 ^ 63) :
    ∀ st : List (Nat × T), (∀ e ∈ st, o ≤ e.1 ∧ e.1 + 32 ≤ o + n) →
      Outside base o n m (stores s₀ base st m)
  | [], _ => fun _ _ => rfl
  | (e, t) :: st, h => by
    intro x hx
    have h₀ := h _ (List.mem_cons_self ..)
    simp only at h₀
    simp only [stores]
    rw [writeW_byte_off _ _ _ _ ?_]
    · exact stores_outside s₀ base m hn st (fun x hx => h x (List.mem_cons_of_mem _ hx)) x hx
    · show 256 / 8 ≤ (x - (base + BitVec.ofNat 64 e)).toNat
      rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat]
      simp only [ofs] at hx
      have := (x - base).isLt
      rw [Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega_arith)]
      omega_arith

theorem mq_eq_word (m : Mem) (base : Addr) (d : Nat) : mq m base d = word m base d := rfl

/-! ## Products -/

/-- What `mul4 a` leaves: the product of the slot `a` and `ymm5–ymm9`, lane by
lane, in `ymm0–ymm4`. -/
def MulPost (base : Addr) (a : Nat) (s s' : State) : Prop :=
  vm s s' = s' ∧ s'.mem = s.mem ∧
    (∀ l < 4, ∀ i < 5, lanes s' 0 l i = mulNat (slotv s.mem base a l) (lanes s 5 l) i ∧
      lanes s' 0 l i < 2 ^ 61) ∧
    (∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)

theorem mul4_wp {a : Nat} (ha : a % 32 = 0) {σ : Sym}
    (he : Sym.init.run (mul4 a) = some σ)
    (hnat : ∀ E l, ∀ k < 5, (σ.reg k).nat E l = mulNat (fun i => E.m (a + 32 * i) l) (fun j => E.v (5 + j) l) k)
    (hok : ∀ k < 5, ∀ l < 4, (σ.reg k).ok (mulB a) l = true ∧ (σ.reg k).bnd (mulB a) l < 2 ^ 61)
    (hkeep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → σ.reg r = .reg r) (hst : σ.st = [])
    {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hx : ∀ l < 4, ∀ i < 5, slotv s.mem base a l i < 2 ^ 52)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) :
    WP isa (.block (mul4 a)) s (MulPost base a s) := by
  have hE : EnvOK s (mulB a) := by
    refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
    · simp only [mulB]
      split
      · rename_i h
        have := hy l hl (r - 5) (by omega_arith)
        simp only [lanes, show 5 + (r - 5) = r by omega_arith] at this
        omega_arith
      · exact lt64 _
    · simp only [mulB]
      split
      · rename_i h
        obtain ⟨i, hi, rfl⟩ : ∃ i < 5, d = a + 32 * i := ⟨(d - a) / 32, by omega_arith, by omega_arith⟩
        have := hx l hl i hi
        simp only [slotv] at this
        omega_arith
      · exact lt64 _
  refine WP.mono (run_ok hc he) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, hst]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => h.keep hr hl (hkeep r hr h1 h2)⟩
  obtain ⟨o, b⟩ := hok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  simp only [lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega_arith⟩
  have hf : (fun i => (envOf s).m (a + 32 * i) l) = slotv s.mem base a l :=
    funext fun j => by rw [envOf_m hs, slotv]
  have hg : (fun j => (envOf s).v (5 + j) l) = lanes s 5 l := funext fun j => rfl
  rw [e, hnat _ _ i hi, hf, hg]

/-- What `mulG` leaves: the product of `ymm10–ymm14` and `ymm5–ymm9`, lane by
lane, in `ymm0–ymm4`, added with `pre` to lanes 0 and 1 of what they held. -/
def MulPostG (pre : Bool) (s s' : State) : Prop :=
  vm s s' = s' ∧ s'.mem = s.mem ∧
    (∀ l < 4, ∀ i < 5, lanes s' 0 l i =
        (if pre = true ∧ l < 2 then lanes s 0 l i else 0) + mulNat (lanes s 10 l) (lanes s 5 l) i ∧
      lanes s' 0 l i < 2 ^ 62 ∧ (pre = false → lanes s' 0 l i < 2 ^ 61)) ∧
    (∀ r < 15, 5 ≤ r → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)

theorem mulGB_env {s : State} {base : Addr} (hs : s.gpr .rdi = base)
    (hp : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 10 l i < 2 ^ 52)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) : EnvOK s mulGB := by
  refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun _ _ _ => lt64 _) (fun _ _ _ => Nat.zero_le _)
  simp only [mulGB]
  split
  · rename_i h
    rcases (by omega_arith : r < 10 ∨ 10 ≤ r) with h' | h'
    · have := hy l hl (r - 5) (by omega_arith)
      simp only [lanes, show 5 + (r - 5) = r by omega_arith] at this
      omega_arith
    · have := hx l hl (r - 10) (by omega_arith)
      simp only [lanes, show 10 + (r - 10) = r by omega_arith] at this
      omega_arith
  · split
    · have := hp l hl r (by omega_arith); simp only [lanes, Nat.zero_add] at this; omega_arith
    · exact lt64 _

theorem mulG0_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 10 l i < 2 ^ 52)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) :
    WP isa (.block (mulG false)) s fun s' => MulPostG false s s' ∧
      ∀ l < 4, qw s' (xr 15) l = qw s (xr 15) l := by
  have hE : EnvOK s mulG0B := by
    refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun _ _ _ => lt64 _) (fun _ _ _ => Nat.zero_le _)
    simp only [mulG0B]
    split
    · rename_i h
      rcases (by omega_arith : r < 10 ∨ 10 ≤ r) with h' | h'
      · have := hy l hl (r - 5) (by omega_arith)
        simp only [lanes, show 5 + (r - 5) = r by omega_arith] at this
        omega_arith
      · have := hx l hl (r - 10) (by omega_arith)
        simp only [lanes, show 10 + (r - 10) = r by omega_arith] at this
        omega_arith
    · exact lt64 _
  refine WP.mono (run_ok hc mulG0_eq) fun s' h => ?_
  refine ⟨⟨h.eq, by rw [h.mem]; exact congrArg (fun st => stores s (s.gpr .rdi) st s.mem) mulG0_st,
    fun l hl i hi => ?_, fun r hr h1 l hl => h.keep (by omega_arith) hl (mulG0_keep r (by omega_arith) h1)⟩,
    fun l hl => h.keep (by decide) hl (mulG0_keep 15 (by decide) (by decide))⟩
  obtain ⟨o, b⟩ := mulG0_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  simp only [lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega_arith, fun _ => by omega_arith⟩
  have hf : (fun i => (envOf s).v (10 + i) l) = lanes s 10 l := funext fun j => rfl
  have hg : (fun j => (envOf s).v (5 + j) l) = lanes s 5 l := funext fun j => rfl
  rw [e]
  show (mulG0.reg i).nat (envOf s) l = _
  rw [mulG0_nat _ _ i hi, hf, hg, mulNatG_eq _ _ _ i hi]
  simp

theorem mulG1_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hp : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 10 l i < 2 ^ 52)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) :
    WP isa (.block (mulG true)) s (MulPostG true s) := by
  have hE := mulGB_env hs hp hx hy
  refine WP.mono (run_ok hc mulG1_eq) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem]; exact congrArg (fun st => stores s (s.gpr .rdi) st s.mem) mulG1_st,
    fun l hl i hi => ?_, fun r hr h1 l hl => h.keep (by omega_arith) hl (mulG1_keep r hr h1)⟩
  obtain ⟨o, b⟩ := mulG1_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  simp only [lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega_arith, fun h => by cases h⟩
  have hf : (fun i => (envOf s).v (10 + i) l) = lanes s 10 l := funext fun j => rfl
  have hg : (fun j => (envOf s).v (5 + j) l) = lanes s 5 l := funext fun j => rfl
  rw [e]
  show (mulG1.reg i).nat (envOf s) l = _
  rw [mulG1_nat _ l hl i hi, hf, hg, mulNatG_eq _ _ _ i hi]
  simp only [true_and, envOf_v]

/-! ## The carries of stages 2 and 3 -/

/-- What stage 2's carry leaves: `ymm10–ymm14` carried. -/
theorem carryU_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : Ctx s) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 10 l i < 2 ^ 63) :
    WP isa (.block (carryT (10 + ·) 15 5 6)) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 10 l i = carryNat (2 ^ 51 - 1) 19 (lanes s 10 l) i ∧
        lanes s' 10 l i < 2 ^ 52) ∧
      (∀ r < 5, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE := carry_env (r := (10 + ·)) (fun i => rfl) hs hk hx
  refine WP.mono (run_ok hc carryU_eq) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, carryU_st]; rfl, fun l hl i hi => ?_,
    fun r hr l hl => h.keep (by omega_arith) hl (carryU_keep r (by omega_arith) (by omega_arith))⟩
  obtain ⟨o, b⟩ := carryU_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  have hs' : (fun j => lanes s 10 l j) = fun j => (envOf s).v (10 + j) l := by
    funext j; simp only [lanes, envOf_v]
  refine ⟨?_, by simp only [lanes]; omega_arith⟩
  simp only [lanes] at e ⊢
  rw [e, carryU_nat _ _ i hi, envOf_m hs, envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']

/-- What stage 3's carry leaves: `ymm0–ymm4` carried, and `ymm10–ymm14` as they were. -/
theorem carryR_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : Ctx s) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 63) :
    WP isa (.block (carryT id 15 5 6)) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i = carryNat (2 ^ 51 - 1) 19 (lanes s 0 l) i ∧
        lanes s' 0 l i < 2 ^ 52) ∧
      (∀ r < 15, 10 ≤ r → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE := carry_env (r := id) (fun i => (Nat.zero_add i).symm) hs hk hx
  refine WP.mono (run_ok hc carryR_eq) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, carryR_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 l hl => h.keep (by omega_arith) hl (carryR_keep r (by omega_arith) (by omega_arith))⟩
  obtain ⟨o, b⟩ := carryR_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  have hs' : (fun j => lanes s 0 l j) = fun j => (envOf s).v j l := by
    funext j; simp only [lanes, Nat.zero_add, envOf_v]
  refine ⟨?_, by simp only [lanes, Nat.zero_add]; omega_arith⟩
  simp only [lanes, Nat.zero_add] at e ⊢
  rw [e, carryR_nat _ _ i hi, envOf_m hs, envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']

/-! ## The stages -/

/-- The bias's limb `j`. -/
def kbv (j : Nat) : Nat := if j = 0 then 2 ^ 62 - 38912 else 2 ^ 62 - 2048

theorem kb_m {m : Mem} {base : Addr} (hk : CConsts m base) {j l : Nat} (hl : l < 4) :
    (mq m base (kb j + 8 * l)).toNat = kbv j := by
  simp only [kb, kbv]; split
  · exact hk.kb0 l hl
  · exact hk.kb1 l hl

/-- The environment of a block that reads products below `2⁶¹` in `ymm0–ymm4`
and the bias. -/
theorem s1aB_env {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) : EnvOK s s1aB := by
  refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun d l hl => ?_)
  · simp only [s1aB]
    split
    · have := hx l hl r (by omega_arith); simp only [lanes, Nat.zero_add] at this; omega_arith
    · exact lt64 _
  · simp only [s1aB]
    split
    · subst_vars; rw [hk.kb0 l hl]
    · split
      · subst_vars; rw [hk.kb1 l hl]
      · exact lt64 _
  · simp only [s1aB]
    split
    · subst_vars; rw [hk.kb0 l hl]
    · split
      · subst_vars; rw [hk.kb1 l hl]
      · exact Nat.zero_le _

/-- Stage 1's differences and sums, limb `i` of lane `l`, from the lanes `x`
(`x l i`), `(x₂, z₂, x₃, z₃)`: `(B, A, D, C)`. -/
def sumDiff (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 0 i + (kbv i - x 1 i)
  | 1 => x 0 i + x 1 i
  | 2 => x 2 i + (kbv i - x 3 i)
  | _ => x 2 i + x 3 i

theorem s1a_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : CConsts s.mem base) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block stage1a) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i = sumDiff (lanes s 0) l i ∧ lanes s' 0 l i < 2 ^ 63) ∧
      (∀ r < 16, 5 ≤ r → ¬ (10 ≤ r ∧ r < 13) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE := s1aB_env hs hk hx
  have e : Sym.init.run stage1a = some s1a := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, s1a_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 h2 l hl => h.keep hr hl (s1a_keep r hr h1 h2)⟩
  obtain ⟨o, b⟩ := s1a_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  simp only [lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega_arith⟩
  rw [e, s1a_nat _ i hi l hl]
  have kbe : (envOf s).m (kb i) = fun l => (mq s.mem base (kb i + 8 * l)).toNat := by
    funext l; rw [envOf_m hs]
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
    simp only [s1aNat, sumDiff, lanes, Nat.zero_add, envOf_v, kbe, kb_m hk (show 0 < 4 by decide),
      kb_m hk (show 2 < 4 by decide)]

/-! ### The mask and the swap -/

theorem mk_wp {s : State} (hc : Ctx s) :
    WP isa (.block vmask) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, qw s' (xr 15) l = s.gpr .rcx) ∧
      (∀ r < 15, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run vmask = some mkS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, mkS_st]; rfl, fun l hl => ?_,
    fun r hr l hl => h.keep (by omega_arith) hl (mkS_keep r hr)⟩
  rw [h.reg _ l hl, xi_xr _ (by decide), mkS_reg]
  simp only [T.eval, ite_true]

theorem xor_mask (x y : BitVec 64) (b : Bool) :
    x ^^^ ((y ^^^ x) &&& VG.Proof.X25519.X86_64.mask b) = if b then y else x := by
  cases b
  · simp [VG.Proof.X25519.X86_64.mask]
  · simp only [VG.Proof.X25519.X86_64.mask, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm y x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem cat_halves (x : BitVec 64) : x.extractLsb' 32 32 ++ x.extractLsb' 0 32 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 32
  · simp [h]
  · simp only [h, decide_false, ite_false, Bool.false_and, decide_eq_true (show j - 32 < 32 by omega_arith),
      Bool.true_and]
    exact congrArg _ (by omega_arith)

/-- `vpermd`'s quadword with the indices of the two doublewords of quadword `q`. -/
theorem pdq_pair (f : Nat → BitVec 64) (i : BitVec 64) (q : Nat) (h0 : (i.extractLsb' 0 3).toNat = 2 * q)
    (h1 : (i.extractLsb' 32 3).toNat = 2 * q + 1) : pdq i f = f q := by
  rw [pdq, h0, h1, dsel, dsel, show (2 * q + 1) / 2 = q by omega_arith, show 2 * q / 2 = q by omega_arith,
    show (2 * q + 1) % 2 = 1 by omega_arith, show 2 * q % 2 = 0 by omega_arith]
  exact cat_halves _

/-- The lane of `(B, A, D, C)` in lane `l` of stage 1's first operand,
`(B, A, C, D)`, or with the swap `(D, C, A, B)`; and of its second,
`(B, A, B, A)`, or with the swap `(D, C, D, C)`. -/
def pu (b : Bool) (l : Nat) : Nat := (if l < 2 then l else 5 - l) ^^^ (if b then 2 else 0)
def pv (b : Bool) (l : Nat) : Nat := l % 2 ^^^ (if b then 2 else 0)

theorem idx_lo (b : Bool) : ∀ l < 4,
    ((((VG.Proof.X25519.X86_64.mask b &&& 0x0000000400000004) ^^^ kiu l).extractLsb' 0 3).toNat = 2 * pu b l ∧
      (((VG.Proof.X25519.X86_64.mask b &&& 0x0000000400000004) ^^^ kiu l).extractLsb' 32 3).toNat =
        2 * pu b l + 1) ∧
    ((((VG.Proof.X25519.X86_64.mask b &&& 0x0000000400000004) ^^^ kiv l).extractLsb' 0 3).toNat = 2 * pv b l ∧
      (((VG.Proof.X25519.X86_64.mask b &&& 0x0000000400000004) ^^^ kiv l).extractLsb' 32 3).toNat =
        2 * pv b l + 1) := by
  cases b <;> decide

/-- What `stage1b` leaves, with the mask of the swap `b` in `ymm15`:
`(B, A, C, D)` in `ymm10–ymm14` and `(B, A, B, A)` in `ymm5–ymm9`, of the
pairs swapped if `b`. -/
theorem s1b_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : Consts s.mem base x1) {b : Bool} (hm : ∀ l < 4, qw s (xr 15) l = VG.Proof.X25519.X86_64.mask b) :
    WP isa (.block stage1b) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 10 l i = lanes s 0 (pu b l) i ∧
        lanes s' 5 l i = lanes s 0 (pv b l) i) := by
  have e : Sym.init.run stage1b = some s1b := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  have ld : ∀ d l, (T.ld d).eval s l = mq s.mem base (d + 8 * l) := fun d l => by
    simp only [T.eval, mq, hs]
  refine ⟨h.eq, by rw [h.mem, s1b_st]; rfl, fun l hl i hi => ⟨?_, ?_⟩⟩
  · have := h.reg (xr (10 + i)) l hl
    rw [xi_xr _ (by omega_arith), s1b_regsU i hi] at this
    simp only [lanes, this]
    simp only [T.eval, idxU, mq, hs] at ld ⊢
    rw [hm l hl]
    have k4 := hk.k4d l hl; have ku := hk.kiu l hl
    simp only [mq] at k4 ku
    rw [k4, ku, pdq_pair _ _ _ (idx_lo b l hl).1.1 (idx_lo b l hl).1.2, Nat.zero_add]
  · have := h.reg (xr (5 + i)) l hl
    rw [xi_xr _ (by omega_arith), s1b_regsV i hi] at this
    simp only [lanes, this]
    simp only [T.eval, idxV, mq, hs] at ld ⊢
    rw [hm l hl]
    have k4 := hk.k4d l hl; have kv := hk.kiv l hl
    simp only [mq] at k4 kv
    rw [k4, kv, pdq_pair _ _ _ (idx_lo b l hl).2.1 (idx_lo b l hl).2.2, Nat.zero_add]

/-! ### Stage 2 -/

/-- Stage 2's first operand from `(BB, AA, CB, DA)` (`x l i`):
`(AA, AA + bias - BB, DA + CB, DA + bias - CB)`. -/
def opU (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 1 i
  | 1 => x 1 i + (kbv i - x 0 i)
  | 2 => x 3 i + x 2 i
  | _ => x 3 i + (kbv i - x 2 i)

theorem s2a_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : CConsts s.mem base) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block stage2a) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 10 l i = opU (lanes s 0) l i ∧ lanes s' 10 l i < 2 ^ 63) ∧
      (∀ r < 5, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE := s1aB_env hs hk hx
  have e : Sym.init.run stage2a = some s2a := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, s2a_st]; rfl, fun l hl i hi => ?_,
    fun r hr l hl => h.keep (by omega_arith) hl (s2a_keep r hr)⟩
  obtain ⟨o, b⟩ := s2a_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  simp only [lanes] at e ⊢
  refine ⟨?_, by omega_arith⟩
  rw [e, s2a_nat _ i hi l hl]
  have kbe : (envOf s).m (kb i) = fun l => (mq s.mem base (kb i + 8 * l)).toNat := by
    funext l; rw [envOf_m hs]
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
    simp only [s2aU, opU, lanes, Nat.zero_add, envOf_v, kbe, kb_m hk (show 1 < 4 by decide),
      kb_m hk (show 3 < 4 by decide)]

theorem topB_env (s : State) : EnvOK s topB :=
  ⟨fun _ _ _ => lt64 _, fun _ => lt64 _, fun _ _ _ => lt64 _, fun _ _ _ => Nat.zero_le _, fun _ _ _ => lt64 _⟩

/-- What `stage2b` leaves: `(0, a24, …)` and lanes 2 and 3 of the first operand in `ymm5–ymm9`. -/
theorem s2b_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : Consts s.mem base x1) :
    WP isa (.block stage2b) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 5 l i =
        if l < 2 then (if i = 0 ∧ l = 1 then 121665 else 0) else lanes s 10 l i) ∧
      (∀ r < 16, (r < 5 ∨ 10 ≤ r) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run stage2b = some s2b := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, s2b_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 l hl => h.keep hr hl (s2b_keep r hr h1)⟩
  obtain ⟨e, _⟩ := h.out (topB_env s) (by omega_arith) hl (s2b_ok i hi l hl)
  have ka := hk.a24 i hi l hl
  simp only [slotv] at ka
  simp only [lanes] at e ⊢
  rw [e, s2b_nat _ i hi l hl, envOf_m hs, ka]
  rfl

/-- What `stage3b` leaves: lanes 0 and 1 of `ymm10–ymm14` with lanes 2 and 3 of
`ymm0–ymm4` in `ymm10–ymm14`, and lanes 0 and 1 of `ymm0–ymm4` with `(1, x₁)`
in `ymm5–ymm9`. -/
theorem s3b_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : Consts s.mem base x1) :
    WP isa (.block stage3b) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5,
        lanes s' 10 l i = (if l < 2 then lanes s 10 l i else lanes s 0 l i) ∧
        lanes s' 5 l i = (if l < 2 then lanes s 0 l i else if l = 3 then x1 i else if i = 0 then 1 else 0)) := by
  have e : Sym.init.run stage3b = some s3b := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, s3b_st]; rfl, fun l hl i hi => ?_⟩
  obtain ⟨o1, o2⟩ := s3b_ok i hi l hl
  obtain ⟨e1, _⟩ := h.out (topB_env s) (by omega_arith) hl o1
  obtain ⟨e2, _⟩ := h.out (topB_env s) (by omega_arith) hl o2
  obtain ⟨n1, n2⟩ := s3b_nat (envOf s) i hi l hl
  have kx := hk.kx1 i hi l hl
  simp only [slotv] at kx
  simp only [lanes, Nat.zero_add] at e1 e2 ⊢
  rw [e1, n1, e2, n2, envOf_m hs, kx]
  refine ⟨rfl, ?_⟩
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> simp [envOf_v]

end VG.Proof.X25519.X86_64.Ifma
