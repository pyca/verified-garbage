module

public import VerifiedGarbage.Proof.Sha3.Seed34
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Absorb
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Arith

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, squeezing

The padded seeds are the states that `Keccak-f` turns into the absorbed ones
(`padded_A0`), and the four states hold them after `absorb4` (`lanes_A0`).
Each `squeeze` permutes the four states (`permute4_ok`) and copies the
first 168 bytes of each to block `n` of its output, at `rbp`, which then
holds the first `168 (n + 1)` bytes of the seed's XOF output (`sq_ok`);
`squeezes` runs them in a loop (`blocks_ok`, `sqs_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Spec.Sha3 (keccakF RC)
open VG.Proof.Sha3 (byteOf Rep xorByte byteOf_xorByte byteOf_xorBytes absorb_pad iterF iterF_succ iterF_keccakF)
open VG.Proof.MlKem (padded xofByte)
open VG.Proof.Sha3.X86_64.X4 (la ba Lanes4 lanes4_of_bytes byte_of_lanes4 Pre4 permute4_ok)

/-! ## The padded seeds -/

export VG.Proof.Sha3.Seed34 (A0 padded_A0 byteOf_A0 xofByte_A0)

theorem B_length (σ : State) (k : Nat) : (B σ k).length = 34 := VG.Proof.Sha3.bytesAt_length _ _ _

/-! ## `Env` after writes -/

/-- `Env` after writes below the saved registers. -/
theorem EnvW.low {σ s s' : State} (he : EnvW w16 σ s) {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨scr σ, oSave⟩)
    (hf : Frame rs s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) : EnvW w16 σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => ((Offset.base_disjoint (scr σ) (k := oSave)
        (e := oSave + 8 * i) (n := 8) (by omega) (by simp only [oSave]; omega)).symm).sub_right (hrs r hr))
      (by decide)]
    exact he.saved i hi
  · refine he.frame.trans (hf.sub fun r hr => ⟨scrR σ, by simp, fun x hx => Offset.sub_base (scr σ) (d := 0)
      (n := oSave) (k := 8192) (by simp only [oSave]; omega) x (by rw [BitVec.add_zero]; exact hrs r hr x hx)⟩)

/-- `Env` after code that writes no memory and keeps its registers. -/
theorem EnvW.keep {σ s s' : State} (he : EnvW w16 σ s) (hm : s'.mem = s.mem) {rs : List Reg} (hk : Keep rs s s')
    (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], r ∉ rs) : EnvW w16 σ s' :=
  EnvW.low he (rs := []) (by simp) (by rw [hm]; exact Frame.refl _ _) hk.2.1 hk.2.2 fun r hr => hk.gpr (hrs r hr)

/-! ## Loops of blocks -/

theorem sx_ofNat {x : Nat} (hx : x < 2 ^ 31) : (BitVec.ofNat 32 x).signExtend 64 = BitVec.ofNat 64 x := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
    omega
  · rw [BitVec.msb_eq_decide]; simp; omega

theorem cnt_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  by_cases hn : n = 0
  · subst hn; rfl
  · simp only [hn, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp at this; omega

theorem cnt_sub (n : Nat) (h₁ : 1 ≤ n) :
    BitVec.ofNat 64 n - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n - 1) := by
  rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h₁]

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl

/-- In a loop of blocks: at block `i`, with `rbp` at `D + step (i - b)` and
`r10` the number of blocks left. -/
def BInv (P : Nat → State → Prop) (D : Addr) (step b n m : Nat) (s : State) : Prop :=
  ∃ i, b ≤ i ∧ i < b + n ∧ m = b + n - i ∧ P i s ∧ s.gpr .rbp = D + BitVec.ofNat 64 (step * (i - b)) ∧
    s.gpr .r10 = BitVec.ofNat 64 (b + n - i)

open VG.Proof.Sha3.X86_64 (wp_mov wp_addi wp_mov32i wp_subi wp_nil) in
/-- `blocks start step n body` from `P b`, where `P` does not depend on
`rbp`, `r10` or the flags, and `body` takes block `i` (with `rbp` at
`rbx + start + step (i - b)`) from `P i` to `P (i + 1)` and keeps `rbp`
and `r10`. -/
theorem blocks_ok {start step b n : Nat} {body : Prog isa} {P : Nat → State → Prop} {s : State}
    (hn : 0 < n) (hn' : n < 2 ^ 31) (hst : start < 2 ^ 31) (hsp : step < 2 ^ 31)
    (hP : ∀ i s s', P i s → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .rbp → r ≠ .r10 → s'.gpr r = s.gpr r) → P i s')
    (hbody : ∀ i t, b ≤ i → i < b + n → P i t →
      t.gpr .rbp = s.gpr .rbx + BitVec.ofNat 64 start + BitVec.ofNat 64 (step * (i - b)) →
      WP isa body t fun t' => P (i + 1) t' ∧ t'.gpr .rbp = t.gpr .rbp ∧ t'.gpr .r10 = t.gpr .r10)
    (h : P b s) : WP isa (blocks start step n body) s (P (b + n)) := by
  unfold blocks
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_mov32i fun s₃ u₃ => wp_nil ?_)
  refine WP.loop (M := isa) (BInv P (s.gpr .rbx + BitVec.ofNat 64 start) step b n) (fun m t ht => ?_) n s₃
    ⟨b, Nat.le_refl _, by omega, by omega, hP _ _ _ h (u₃.mem.trans (u₂.mem.trans u₁.mem))
      (u₃.rd.trans (u₂.rd.trans u₁.rd)) (u₃.wr.trans (u₂.wr.trans u₁.wr))
      (fun r h₁ h₂ => (u₃.other r h₂).trans ((u₂.other r h₁).trans (u₁.other r h₁))), ?_, ?_⟩
  · obtain ⟨i, hb, hi, rfl, hPi, hbp, h10⟩ := ht
    refine WP.seq (WP.mono (hbody i t hb hi hPi hbp) fun t₁ ⟨hP₁, bp₁, r₁⟩ =>
      wp_addi fun t₂ u₂ => wp_subi fun t₃ u₃ z₃ => wp_nil ?_)
    have hP₃ : P (i + 1) t₃ := hP _ _ _ hP₁ (u₃.mem.trans u₂.mem) (u₃.rd.trans u₂.rd) (u₃.wr.trans u₂.wr)
      fun r h₁ h₂ => (u₃.other r h₂).trans (u₂.other r h₁)
    have c₃ : t₂.gpr .r10 - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (b + n - i - 1) := by
      rw [u₂.other _ (by decide), r₁, h10, cnt_sub _ (by omega)]
    rw [eval_ne, z₃, c₃, cnt_zero (by omega)]
    by_cases hl : b + n - i - 1 = 0
    · left
      refine ⟨by simp [hl], ?_⟩
      rw [show b + n = i + 1 by omega]
      exact hP₃
    · right
      refine ⟨by simp [hl], b + n - (i + 1), by omega, i + 1, by omega, by omega, rfl, hP₃, ?_, ?_⟩
      · rw [u₃.other _ (by decide), u₂.gpr, bp₁, hbp, sx_ofNat hsp,
          BitVec.add_assoc (s.gpr .rbx + BitVec.ofNat 64 start), BitVec.ofNat_add_ofNat,
          show i + 1 - b = (i - b) + 1 by omega, Nat.mul_succ]
      · rw [u₃.gpr, c₃, show b + n - i - 1 = b + n - (i + 1) by omega]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, sx_ofNat hst, Nat.sub_self, Nat.mul_zero, add_ofNat_zero]
  · rw [u₃.gpr, show b + n - b = n by omega]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

/-! ## The squeezes -/

/-- After `n` squeezes. -/
structure SqInvW (w16 : Bool) (σ : State) (n : Nat) (s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) fun k => iterF n (A0 (B σ k))
  buf : ∀ k < 4, ∀ p < 168 * n, s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) p

theorem lanes_A0 {σ : State} {m : Mem} (h : SB σ m (PF σ)) : Lanes4 m (scr σ) fun k => iterF 0 (A0 (B σ k)) :=
  lanes4_of_bytes fun k hk q hq => by
    rw [h k hk q hq, show iterF 0 (A0 (B σ k)) = A0 (B σ k) from rfl, byteOf_A0 (B_length σ k) hq, PF]



theorem la_tbl (σ : State) (r k : Nat) : la (at' σ 1600) r k = la (scr σ) (50 + r) k := by
  rw [la, la, at', Offset.add_add, show 1600 + (32 * r + 8 * k) = 32 * (50 + r) + 8 * k by omega]

theorem sx800 : BitVec.signExtend 64 (BitVec.ofNat 32 oTmp) = BitVec.ofNat 64 800 := by decide
theorem sx1600 : BitVec.signExtend 64 (BitVec.ofNat 32 oRc) = BitVec.ofNat 64 1600 := by decide
theorem sx2368 : BitVec.signExtend 64 (BitVec.ofNat 32 oBuf) = BitVec.ofNat 64 2368 := by decide

theorem args_ok {σ s : State} (he : EnvW w16 σ s) :
    WP isa (.block permArgs) s fun s' => (s'.mem = s.mem ∧ s'.gpr .rdi = scr σ ∧ s'.gpr .rsi = at' σ 800 ∧
      s'.gpr .rdx = at' σ 1600 ∧ s'.gpr .rcx = at' σ 2368) ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold permArgs
  xrun [he.rbx, sx800, sx1600, sx2368]

/-- The permutation's precondition, in the scratch space. -/
theorem pre4 {σ : State} (hp : PreW w16 σ) {s : State} (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr)
    (hrc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r) :
    Pre4 s (scr σ) (at' σ 800) (at' σ 1600) :=
  ⟨fun i _ => in_scr hp hwr (a := 32 * i) (by omega),
    fun i _ => by rw [at', Offset.add_add]; exact in_scr hp hwr (by omega),
    fun r _ => by rw [at', Offset.add_add]; exact in_scr' hp hrd hwr (by omega),
    Offset.base_disjoint _ (by omega) (by omega),
    Offset.base_disjoint _ (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    fun r hr k hk => by rw [la_tbl]; exact hrc r hr k hk⟩

/-- A buffer byte, read through a frame of the states. -/
theorem buf_frame {σ : State} {m m' : Mem} {rs : List Region}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨at' σ oBuf, 2016⟩ r) (hf : Frame rs m m') {k p : Nat} (hk : k < 4)
    (hp' : p < 504) : m' (at' σ (oBuf + 504 * k + p)) = m (at' σ (oBuf + 504 * k + p)) := by
  have := hf.bytes (R := ⟨at' σ oBuf, 2016⟩) hd (by simp only; omega) (i := 504 * k + p) (by simp only; omega)
  simpa only [at', Offset.add_add, Nat.add_assoc] using this

/-- The permutation, after `n` squeezes. -/
theorem perm_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {n : Nat} (hn : n < 3) {s : State} (h : SqInvW w16 σ n s)
    {rest : Prog isa} {Q : State → Prop} (kont : ∀ s', EnvW w16 σ s' ∧ s'.gpr .r14 = 1 ∧
      (∀ r < 24, ∀ k < 4, s'.mem.readW (la (scr σ) (50 + r) k) 64 = RC r) ∧
      Lanes4 s'.mem (scr σ) (fun k => iterF (n + 1) (A0 (B σ k))) ∧
      (∀ k < 4, ∀ p < 168 * n, s'.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) p) ∧
      s'.gpr .rbp = s.gpr .rbp ∧ s'.gpr .r10 = s.gpr .r10 → WP isa rest s' Q) :
    WP isa (.seq (.block permArgs) (.seq (Impl.Sha3.X86_64.X4.permute4 fast) rest)) s Q := by
  refine WP.seq (WP.mono (args_ok h.env) fun s₁ ⟨⟨hm, hdi, hsi, hdx, hcx⟩, k₁⟩ => ?_)
  have hrd : s₁.rd = σ.rd := k₁.2.1.trans h.env.rd
  have hwr : s₁.wr = σ.wr := k₁.2.2.trans h.env.wr
  refine WP.seq (WP.mono (permute4_ok (fast := fast) (A := fun k => iterF n (A0 (B σ k))) (pre4 hp hrd hwr (by rw [hm]; exact h.rc))
    hdi hsi hdx (by rw [hcx, at', at', Offset.add_add]) (by rw [hm]; exact h.lanes))
    fun s₂ ⟨hl, hf, hrd₂, hwr₂, _, hg⟩ => kont s₂ ?_)
  have hsub : ∀ r ∈ [(⟨scr σ, 800⟩ : Region), ⟨at' σ 800, 800⟩], Region.Sub r ⟨scr σ, oSave⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by simp only [oSave]; omega)
    · exact Offset.sub_base _ (by simp only [oSave]; omega)
  refine ⟨EnvW.low (h.env.keep hm k₁ (by decide)) hsub hf hrd₂ hwr₂ fun r hr => hg r
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide) (by decide), k₁.gpr (by decide), h.r14], fun r hr k hk => ?_, ?_, fun k hk p hp' => ?_,
    by rw [hg _ (by decide) (by decide), k₁.gpr (by decide)], by rw [hg _ (by decide) (by decide), k₁.gpr (by decide)]⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega),
          Offset.disjoint (scr σ) (d := 32 * (50 + r) + 8 * k) (n := 8) (e := 800) (k := 800) (by omega) (by omega)
            (by omega)⟩) (by decide), hm]
    exact h.rc r hr k hk
  · intro i hi k hk
    rw [hl i hi k hk]
    rfl
  · rw [buf_frame (by simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := oBuf) (n := 2016) (by simp only [oBuf]; omega)
        (by simp only [oBuf]; omega), Offset.disjoint (scr σ) (d := oBuf) (n := 2016) (e := 800) (k := 800)
          (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by omega)⟩) hf hk (by omega), hm]
    exact h.buf k hk p hp'


/-! ## Copying the output -/

/-- During the copy of block `n`: the first `I` lanes of state `K` copied,
and all of the states before it. -/
structure EXIW (w16 : Bool) (σ : State) (n K I : Nat) (s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) (fun k => iterF (n + 1) (A0 (B σ k)))
  buf : ∀ k < 4, ∀ p < 504, (p < 168 * n ∨ (168 * n ≤ p ∧ p < 168 * n + 168 ∧ (k < K ∨ (k = K ∧ p < 168 * n + 8 * I)))) →
    s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) p
  rbp : s.gpr .rbp = at' σ (oBuf + 168 * n)

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem ext_step {σ : State} (hp : PreW w16 σ) {n K I : Nat} (hn : n < 3) (hK : K < 4) (hI : I < 21) {s : State}
    (h : EXIW w16 σ n K I s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))),
      .store (at_ .rbp (504 * K + 8 * I)) .rax]) s (EXIW w16 σ n K (I + 1)) := by
  refine wp_movm (a := at' σ (32 * I + 8 * K)) (by rw [ea_at, h.env.rbx])
    (in_scr' hp h.env.rd h.env.wr (by omega)) fun s₁ u₁ => wp_store (a := at' σ (oBuf + 504 * K + 168 * n + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.rbp, at', at', Offset.add_add,
        show oBuf + 168 * n + (504 * K + 8 * I) = oBuf + 504 * K + 168 * n + 8 * I by omega])
      (by rw [u₁.wr]; exact in_scr hp h.env.wr (by simp only [oBuf]; omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (oBuf + 504 * K + 168 * n + 8 * I)) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  have hf : Frame [⟨at' σ (oBuf + 504 * K + 168 * n + 8 * I), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨EnvW.low h.env (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base _ (by simp only [oBuf, oSave]; omega)) hf (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by
        rw [g₂, u₁.other r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)],
    by rw [g₂, u₁.other _ (by decide), h.r14], fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' hc => ?_,
    by rw [g₂, u₁.other _ (by decide), h.rbp]⟩
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) (d := 32 * (50 + r) + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) (d := 32 * i + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.lanes i hi k hk)
  · rw [hm]
    by_cases hw : k = K ∧ 168 * n + 8 * I ≤ p ∧ p < 168 * n + 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [wb_in _ _ _ (by omega) (by simp only [oBuf]; omega) (by decide),
        show 8 * (oBuf + 504 * k + p - (oBuf + 504 * k + 168 * n + 8 * I)) = 8 * (p - 168 * n - 8 * I) by omega,
        byte_readW _ _ (by omega), at', Offset.add_add,
        show 32 * I + 8 * k + (p - 168 * n - 8 * I) = 32 * ((8 * I + (p - 168 * n - 8 * I)) / 8) + 8 * k +
          (8 * I + (p - 168 * n - 8 * I)) % 8 by omega,
        byte_of_lanes4 h.lanes hk (by omega), ← xofByte_A0 (B_length σ k) (by omega),
        show 168 * n + (8 * I + (p - 168 * n - 8 * I)) = p by omega]
    · rw [wb_out _ _ _ (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by simp only [oBuf]; omega)]
      exact h.buf k hk p hp' (by omega)

theorem extract_eq : extract = (List.range 4).flatMap fun K => (List.range 21).flatMap fun I =>
    [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))), .store (at_ .rbp (504 * K + 8 * I)) .rax] := rfl

/-- Block `n` of each state's output. -/
theorem extract_ok {σ : State} (hp : PreW w16 σ) {n : Nat} (hn : n < 3) {s : State} (h : EXIW w16 σ n 0 0 s) :
    WP isa (.block extract) s (SqInvW w16 σ (n + 1)) := by
  rw [extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => EXIW w16 σ n K 0 s) (fun K s hK h => ?_) 4 (Nat.le_refl _) s h)
    fun s' h' => ⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' => h'.buf k hk p (by omega) (by omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun I s => EXIW w16 σ n K I s) (fun I s hI h => ext_step hp hn hK hI h)
    21 (Nat.le_refl _) s h) fun s' h' =>
      ⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' hc => h'.buf k hk p hp' (by omega), h'.rbp⟩

/-- `squeeze`, to block `n`: after `n + 1` squeezes, with `rbp` and `r10` kept. -/
theorem sq_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {n : Nat} (hn : n < 3) {s : State} (h : SqInvW w16 σ n s)
    (hbp : s.gpr .rbp = at' σ (oBuf + 168 * n)) :
    WP isa (squeeze fast) s fun s' => SqInvW w16 σ (n + 1) s' ∧ s'.gpr .rbp = s.gpr .rbp ∧ s'.gpr .r10 = s.gpr .r10 := by
  unfold squeeze
  exact perm_ok (fast := fast) hp hn h fun s' ⟨he, h14, hrc, hl, hb, h₁, h₂⟩ =>
    WP.mono (WP.keep [.rax] (extract_ok hp hn ⟨he, h14, hrc, hl, fun k hk p _ hc => hb k hk p (by omega),
      by rw [h₁, hbp]⟩) (by decide)) fun s'' ⟨h', k⟩ =>
        ⟨h', by rw [k.gpr (by decide), h₁], by rw [k.gpr (by decide), h₂]⟩

/-- `SqInv` does not depend on `rbp`, `r10` or the flags. -/
theorem SqInvW.frame {σ : State} {n : Nat} {s s' : State} (h : SqInvW w16 σ n s) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r, r ≠ .rbp → r ≠ .r10 → s'.gpr r = s.gpr r) :
    SqInvW w16 σ n s' := by
  have k : Keep [.rbp, .r10] s s' := ⟨fun r hr => hg r (fun e => hr (by simp [e])) (fun e => hr (by simp [e])), hrd, hwr⟩
  exact ⟨h.env.keep hm k (by decide), by rw [k.gpr (by decide), h.r14], by rw [hm]; exact h.rc,
    by rw [hm]; exact h.lanes, by rw [hm]; exact h.buf⟩

/-- `squeezes b n`: after `b + n` squeezes. -/
theorem sqs_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {b n : Nat} (hn : 0 < n) (hbn : b + n ≤ 3) {s : State}
    (h : SqInvW w16 σ b s) : WP isa (squeezes b n fast) s (SqInvW w16 σ (b + n)) := by
  unfold squeezes
  refine blocks_ok hn (by omega) (by simp only [oBuf]; omega) (by decide) (fun _ _ _ h => h.frame)
    (fun i t hb hi hi' hbp => sq_ok hp (by omega) hi' ?_) h
  rw [hbp, h.env.rbx, Offset.add_add, at', show oBuf + 168 * b + 168 * (i - b) = oBuf + 168 * i by
    rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' hb]]

end VG.Proof.MlKem.X86_64.S4
