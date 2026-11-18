module

public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.RISCV64.Freeze
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarReduce
import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.X25519.Limbs
import VerifiedGarbage.Proof.X25519.RISCV64.Freeze
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Field
public import VerifiedGarbage.Proof.Ed25519.RecoverResult
import VerifiedGarbage.Proof.X25519.RISCV64.Bits
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Recover
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Freeze
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Ed25519.Recover
public import VerifiedGarbage.Proof.X25519.Invert
public import VerifiedGarbage.Proof.X25519.Field32Contract
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed25519.RISCV64.MulFn
public import VerifiedGarbage.Proof.Ed25519.Point32Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.Ed25519.RISCV64.FieldMemory
public import VerifiedGarbage.Spec.Ed25519
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Power
public import VerifiedGarbage.Proof.X25519.Chain250
import VerifiedGarbage.Proof.X25519.RISCV64.R64.Reduce

/-! ### `Ed25519.RISCV64.RecoverCand`, which this module and modules that import it used -/

section

/-! ### `Ed25519.RISCV64.Encode`, which this module and modules that import it used -/

section

/-! ### `Ed25519.RISCV64.SpecConv`, which this module and modules that import it used -/

section

/-! ### `Ed25519.RISCV64.Power`, which this module and modules that import it used -/

section

/-!
# Ed25519 on RISCV64: the addition chain to `z^(2^250 - 1)` and `z^11`

`chain250` with inlined products (`PSpec`): it changes no register but the
counter `t1` and the field code's `clob64`, and no memory but bytes 512 to 1023 of the
working space (`PR`: slots 14 to 17 and the product's limbs), and maps the
slots by `power250Env`, whose slots 15 and 14 are `chainF`'s results.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519 (sqn)
open VG.Proof.X448.RISCV64.R64 (clob64)

def opMul (o a b : Slot) (e : Env) : Env := Function.update e o (e a * e b)

def opSqn (o a : Slot) (n : Nat) (e : Env) : Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Slot) (e : Env) (v : Spec.X25519.Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

/-- What the chain writes: bytes 512 to 1023 of the working space. -/
abbrev PR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 512, 512⟩

/-- `c` maps the slots by `f`, changing no register but `t1` and `clob64`
and no memory but `PR`. -/
def PSpec (b : Addr) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Ctx b s → WP isa c s fun t =>
    Rest (.t1 :: clob64) s t ∧ Frame [PR b] s.mem t.mem ∧ env t.mem b = f (env s.mem b)

theorem PSpec.seq {b : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env}
    (h₁ : PSpec b c₁ f) (h₂ : PSpec b c₂ g) : PSpec b (.seq c₁ c₂) fun e => g (f e) :=
  fun s hc => WP.seq (WP.mono (h₁ s hc) fun _ ⟨r₁, f₁, e₁⟩ =>
    WP.mono (h₂ _ (hc.of_rest r₁ (by decide))) fun _ ⟨r₂, f₂, e₂⟩ =>
      ⟨r₁.trans r₂, f₁.trans f₂, by rw [e₂, e₁]⟩)

theorem frame_PR {b : Addr} {o : Slot} (ho : 14 ≤ o.val) {m m' : Mem}
    (hf : Frame (opFrame b (offset o)) m m') : Frame [PR b] m m' := by
  have hs := slot_range o
  have hA := eACC_eq
  have ho' : 512 ≤ offset o := by simp only [offset]; omega_arith
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.sub _ (by omega_arith) (by omega_arith)
  · exact Offset.sub _ (by omega_arith) (by omega_arith)

theorem mulP_ok {b : Addr} {s : State} (hc : Ctx b s) (o x y : Slot) (ho : 14 ≤ o.val) :
    WP isa (mulP o x y) s fun t =>
      Rest clob64 s t ∧ Frame [PR b] s.mem t.mem ∧ env t.mem b = opMul o x y (env s.mem b) := by
  have hA := eACC_eq
  have h1 := slot_range o
  have h2 := slot_range x
  have h3 := slot_range y
  refine WP.mono (R64.mulAt_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using []) hc)
    fun t ⟨hr, hf, hv⟩ => ⟨hr, frame_PR ho hf, ?_⟩
  rw [field_update o (by omega_using [hA]) (by omega_using [hA]) hf]
  exact congrArg _ (Proof.X25519.toFe_mul hv)

theorem mulPS (b : Addr) (o x y : Slot) (ho : 14 ≤ o.val) : PSpec b (mulP o x y) (opMul o x y) :=
  fun _ hc => WP.mono (mulP_ok hc o x y ho) fun _ ⟨r, f, e⟩ => ⟨r.mono (by decide), f, e⟩

theorem sqLoop_ok {s₀ : State} {b : Addr} (hc : Ctx b s₀) (o : Slot) (ho : 14 ≤ o.val)
    (x : Spec.X25519.Fe) (n : Nat) (hn : n < 2048) :
    ∀ m s, 1 ≤ m → m ≤ n → Rest (.t1 :: clob64) s₀ s → Frame [PR b] s₀.mem s.mem →
      s.gpr .t1 = BitVec.ofNat 64 m →
      env s.mem b = Function.update (env s₀.mem b) o (sqn x (n - m)) →
      WP isa (.loop (.seq (mulP o o o) (.block [.addi .t1 .t1 (-1)])) (.nonzero .t1)) s fun t =>
        Rest (.t1 :: clob64) s₀ t ∧ Frame [PR b] s₀.mem t.mem ∧
        env t.mem b = Function.update (env s₀.mem b) o (sqn x n) := by
  intro m s h1 h2 hr hf hb he
  refine WP.loop (M := isa) (fun m (s : State) =>
    1 ≤ m ∧ m ≤ n ∧ Rest (.t1 :: clob64) s₀ s ∧ Frame [PR b] s₀.mem s.mem ∧
    s.gpr .t1 = BitVec.ofNat 64 m ∧
    env s.mem b = Function.update (env s₀.mem b) o (sqn x (n - m))) ?_
    m s ⟨h1, h2, hr, hf, hb, he⟩
  intro m s ⟨h1, h2, hr, hf, hb, he⟩
  have hcs : Ctx b s := hc.of_rest hr (by decide)
  refine WP.seq (WP.mono (mulP_ok hcs o o o ho) fun s1 ⟨r1, f1, e1⟩ => ?_)
  refine wp_subi (by decide) fun s2 u2 => WP.block_nil ?_
  have b2 : s2.gpr .t1 = BitVec.ofNat 64 (m - 1) := by
    rw [u2.gpr, r1.gpr _ (by decide), hb, ofNat_sub_one h1 (by omega_arith)]
  have k2 : Rest (.t1 :: clob64) s₀ s2 := hr.trans ((r1.mono (by decide)).trans (u2.rest (by decide)))
  have f2 : Frame [PR b] s₀.mem s2.mem := by rw [u2.mem]; exact hf.trans f1
  have e2 : env s2.mem b = Function.update (env s₀.mem b) o (sqn x (n - (m - 1))) := by
    rw [u2.mem, e1, he, opMul_update]
    apply congrArg (Function.update (env s₀.mem b) o)
    rw [show n - (m - 1) = (n - m) + 1 by omega_arith]
    rfl
  have hz : (s2.gpr .t1 != 0) = decide (m - 1 ≠ 0) := by rw [b2, ofNat_ne_zero (by omega_arith)]
  rw [eval_nonzero, hz]
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by simp [hm], k2, f2, by rw [e2, hm, Nat.sub_zero]⟩
  · exact .inr ⟨by simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, k2, f2, b2, e2⟩

theorem sqnS (b : Addr) (o a : Slot) (n : Nat) (ho : 14 ≤ o.val) (hn : 2 ≤ n) (hn' : n < 2048) :
    PSpec b (Impl.Ed25519.RISCV64.sqn o a n) (opSqn o a n) := by
  intro s hc
  refine WP.seq (WP.mono (mulP_ok hc o a a ho) fun s1 ⟨r1, f1, e1⟩ => ?_)
  refine WP.seq (wp_li (by omega_arith) fun s2 u2 => WP.block_nil ?_)
  have k2 : Rest (.t1 :: clob64) s s2 := (r1.mono (by decide)).trans (u2.rest (by decide))
  refine sqLoop_ok hc o ho (env s.mem b a) n hn' (n - 1) s2 (by omega_arith) (by omega_arith) k2
    (by rw [u2.mem]; exact f1) u2.gpr ?_
  rw [u2.mem, e1, show n - (n - 1) = 1 by omega_arith]
  rfl

def power250Env (e : Env) : Env :=
  opMul 15 16 15 (opSqn 16 16 50 (opMul 16 17 16 (opSqn 17 16 100
    (opMul 16 16 15 (opSqn 16 15 50 (opMul 15 16 15 (opSqn 16 16 10 (opMul 16 17 16 (opSqn 17 16 20
    (opMul 16 16 15 (opSqn 16 15 10 (opMul 15 16 15 (opSqn 16 15 5 (opMul 15 15 16
    (opMul 16 14 14 (opMul 14 14 15 (opMul 15 2 15 (opMul 15 15 15 (opMul 15 14 14
    (opMul 14 2 2 e))))))))))))))))))))

theorem chain250S (b : Addr) : PSpec b chain250 power250Env :=
  (mulPS b 14 2 2 (by decide)).seq <|
  (mulPS b 15 14 14 (by decide)).seq <|
  (mulPS b 15 15 15 (by decide)).seq <|
  (mulPS b 15 2 15 (by decide)).seq <|
  (mulPS b 14 14 15 (by decide)).seq <|
  (mulPS b 16 14 14 (by decide)).seq <|
  (mulPS b 15 15 16 (by decide)).seq <|
  (sqnS b 16 15 5 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 15 16 15 (by decide)).seq <|
  (sqnS b 16 15 10 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 16 15 (by decide)).seq <|
  (sqnS b 17 16 20 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 17 16 (by decide)).seq <|
  (sqnS b 16 16 10 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 15 16 15 (by decide)).seq <|
  (sqnS b 16 15 50 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 16 15 (by decide)).seq <|
  (sqnS b 17 16 100 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 17 16 (by decide)).seq <|
  (sqnS b 16 16 50 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 15 16 15 (by decide))

theorem power250Env_eval (e : Env) :
    power250Env e 15 = (Proof.X25519.chainF (e 2)).1 ∧ power250Env e 14 = (Proof.X25519.chainF (e 2)).2 := by
  simp only [power250Env, opMul, opSqn, Function.update_apply]
  simp only [↓reduceIte, Fin.isValue, Fin.reduceEq]
  exact ⟨rfl, rfl⟩

/-- `vg_gf25519_r32_pow250`'s code, from the working space in `a0`, a multiple of 8. -/
theorem pow250Fn_ok {b : Addr} {s : State} (h3 : s.gpr .a0 = b) (hal : b.toNat % 8 = 0)
    (hw : (⟨b, 4096⟩ : Region) ∈ s.wr) :
    WP isa pow250Fn s fun t =>
      Rest (.a3 :: .t1 :: clob64) s t ∧ Frame [PR b] s.mem t.mem ∧ env t.mem b = power250Env (env s.mem b) := by
  refine WP.seq (wp_mv fun s1 u1 => WP.block_nil ?_)
  have hc : Ctx b s1 := ⟨by rw [u1.gpr, h3], hal, fun d n hd => by
    rw [u1.wr]; exact in_base hw (by omega_using [hd]) (by omega_using [hd])⟩
  refine WP.mono (chain250S b s1 hc) fun t ⟨hr, hf, he⟩ => ⟨?_, by rw [u1.mem] at hf; exact hf, by rw [he, u1.mem]⟩
  exact (u1.rest (by decide)).trans (hr.mono (by decide))

end VG.Proof.Ed25519.RISCV64

end

end

/-!
# Ed25519 on RISC-V: the elements as the contracts read them

What `Base`, `MulFn` and `PointAdd` do not already state: the contracts'
`valAt` of a slot is the proofs' `V` (`valAt_ofNat`), `pow250`'s `Keeps₂`
follows from its frame (`keeps_pow`), and a power of `env` is the
contracts' power of `V` (`val_of_env`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P)

theorem valAt_ofNat (m : Mem) (b : Addr) (i : Slot) :
    Proof.X25519.Field32.valAt m b (BitVec.ofNat 32 (offset i)) = V m b (offset i) := by
  have := slot_range i
  rw [valAt_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this]), ← read_V, ← read_V, BitVec.add_zero]

/-- `pow250`'s `Keeps₂`, from its frame. -/
theorem keeps_pow {b : Addr} {m m' : Mem} (hf : Frame [PR b] m m') : Proof.X25519.Field32.Keeps₂ b m m' := by
  intro i hi hown
  simp only [Proof.X25519.Field32.wsBytes, Proof.X25519.Field32.eAt, Proof.X25519.Field32.ownEnd] at hi hown
  exact hf _ fun r hr => by rw [List.mem_singleton.mp hr]; exact byte_out (by omega_using [hi]) (by omega_using []) hown

/-- A power, as the contract states it. -/
theorem val_of_env {m m' : Mem} {b : Addr} {i j : Slot} {e : Nat}
    (h : env m' b i = Proof.X25519.pw (env m b j) e) :
    V m' b (offset i) % P = V m b (offset j) ^ e % P := by
  have := congrArg Fin.val h
  simp only [env, FS, Proof.X25519.toFe_val, Proof.X25519.pw, Fin.val_ofNat] at this
  rw [this, ← Nat.pow_mod]

end VG.Proof.Ed25519.RISCV64

end

end

/-! ### `Ed25519.RISCV64.FieldVerified`, which only this module used -/

section

/-!
# `vg_gf25519_r32_pow250` on RISC-V, by register

`pow250` meets a contract of its facts by register (`powRV`, `pow_ok'`), with
no stack, from a working space aligned to 8 bytes, as an `[u64]` is
(`RISCV64.abi`'s `alignsBufs`): the callers in this library call it through
this. It calls no other function and writes no callee-saved register or `ra`
(`WP.keep`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P)
open VG.Proof.X25519.Field32 (valAt Fits Keeps Keeps₂)

/-- The registers the functions may write. -/
def fnWrites : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

/-- The working space of `pow250` and the point addition, `bytes` long and aligned, in `a0`. -/
def wsPre (bytes : Nat) (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .a0, bytes⟩] ∧ (s.gpr .a0).toNat % 8 = 0

def wsPub (s₁ s₂ : State) : Prop := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.sp = s₂.sp

/-- `pow250`'s facts by register: `a^(2^250 - 1)` and `a^11` from `a`, the rest of the
working space kept. -/
def powRV : Contract isa where
  pre := wsPre 4096
  post s s' :=
    valAt s'.mem (s.gpr .a0) (BitVec.ofNat 32 Proof.X25519.Field32.oAt) % P =
        valAt s.mem (s.gpr .a0) (BitVec.ofNat 32 Proof.X25519.Field32.aAt) ^ (2 ^ 250 - 1) % P ∧
      valAt s'.mem (s.gpr .a0) (BitVec.ofNat 32 Proof.X25519.Field32.eAt) % P =
        valAt s.mem (s.gpr .a0) (BitVec.ofNat 32 Proof.X25519.Field32.aAt) ^ 11 % P ∧
      Keeps₂ (s.gpr .a0) s.mem s'.mem
  pub := wsPub

theorem pow_ok' (s : State) (hs : powRV.pre s) :
    ∃ t s', Exec isa pow250Fn s t s' ∧ abiPreserved s s' ∧ powRV.post s s' := by
  obtain ⟨_, hwr, hal⟩ := hs
  obtain ⟨t, s', he, ⟨_, hF, hE⟩, hk⟩ := WP.keep fnWrites
    (pow250Fn_ok (s := s) rfl hal (by rw [hwr]; exact List.mem_singleton_self _)) (by decide +kernel)
  have h15 : env s'.mem (s.gpr .a0) 15 = Proof.X25519.pw (env s.mem (s.gpr .a0) 2) (2 ^ 250 - 1) := by
    rw [congrFun hE 15, (power250Env_eval _).1, Proof.X25519.chainF_eq]
  have h14 : env s'.mem (s.gpr .a0) 14 = Proof.X25519.pw (env s.mem (s.gpr .a0) 2) 11 := by
    rw [congrFun hE 14, (power250Env_eval _).2, Proof.X25519.chainF_eq]
  refine ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), ?_, ?_, keeps_pow hF⟩
  · rw [show Proof.X25519.Field32.oAt = offset 15 from rfl, show Proof.X25519.Field32.aAt = offset 2 from rfl,
      valAt_ofNat, valAt_ofNat]
    have h := val_of_env h15
    exact h
  · rw [show Proof.X25519.Field32.eAt = offset 14 from rfl, show Proof.X25519.Field32.aAt = offset 2 from rfl,
      valAt_ofNat, valAt_ofNat]
    exact val_of_env (e := 11) h14

end VG.Proof.Ed25519.RISCV64

end

end


/-!
# Ed25519 on RISCV64: inversion and encoding

A call of `vg_gf25519_r32_pow250` (`power250_ok`), the inversion of slot 2
into slot 15 (`invert_ok`: the chain, five squarings, a product), the
affine coordinates (`pointAffine_ok`), and the encoding of the point at
`FR` (`pointEncode_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519
open VG.Spec.X25519 (P)
open VG.Proof.X25519 (pw sqn)
open VG.Proof.X448.RISCV64.R64 (clob64)

/-- A slot's element from the residue of its value. -/
theorem env_of_val {m m' : Mem} {b : Addr} {i j : Slot} {e : Nat}
    (h : V m' b (offset i) % P = V m b (offset j) ^ e % P) : env m' b i = pw (env m b j) e := by
  apply Fin.ext
  simp only [env, FS, Proof.X25519.toFe_val, pw, Fin.val_ofNat]
  rw [h, ← Nat.pow_mod]

/-- The slots below `pow250`'s results keep their elements. -/
theorem env_keeps₂ {b : Addr} {m m' : Mem} (h : Proof.X25519.Field32.Keeps₂ b m m') {i : Slot} (hi : i.val < 14) :
    env m' b i = env m b i := by
  have hs := slot_range i
  unfold env FS
  rw [← read_V, ← read_V]
  refine congrArg (fun v : BitVec (8 * 32) => Proof.X25519.toFe v.toNat) (Mem.read_congr fun j hj => ?_)
  have ho : offset i = 64 + 32 * i.val := rfl
  rw [Offset.add_add]
  exact h (offset i + j) (by simp only [Proof.X25519.Field32.wsBytes]; omega_arith)
    (by simp only [Proof.X25519.Field32.eAt]; omega_arith)

/-- `vg_gf25519_r32_pow250` never writes `a0`. -/
theorem pow250Fn_a0 : ∀ i ∈ instrs pow250Fn, dstOf i ≠ some Reg.a0 := by
  have nw : ((instrs pow250Fn).all fun i => dstOf i != some Reg.a0) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp nw i hi

/-- **A call of `vg_gf25519_r32_pow250`**: slot 15 `z^(2^250 - 1)` and slot 14 `z^11`, for `z` in
slot 2; slots 0–13 kept. -/
theorem power250_ok {b : Addr} {s : State} (hc : Ctx8 b s) :
    WP isa power250 s fun t => Keep b s t ∧
      env t.mem b 15 = pw (env s.mem b 2) (2 ^ 250 - 1) ∧ env t.mem b 14 = pw (env s.mem b 2) 11 ∧
      ∀ i : Slot, i.val < 14 → env t.mem b i = env s.mem b i := by
  unfold power250
  refine WP.seq (wp_mv fun s1 u1 => WP.block_nil ?_)
  have e0 : s1.gpr .a0 = b := by rw [u1.gpr, hc.a3]
  have hr1 : Rest [.a0] s s1 := u1.rest (by decide)
  have g : ∀ q, q ∉ linkRegs → (s1.callEntry.withRegions [] [⟨b, 4096⟩]).gpr q = s1.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hw1 : Covers [⟨b, 4096⟩] s1.wr := hc.ws.of_rest hr1
  refine WP.seq (WP.call (k := powRV) pow_ok' (rd := []) (wr := [⟨b, 4096⟩])
    ⟨rfl, by rw [g _ (by decide), e0]; rfl,
      by rw [g _ (by decide), e0]; exact hc.al⟩
    (by rw [List.nil_append]; exact hw1.right) hw1 ?_ (by decide +kernel))
  intro t hrd hwr hsp hfr hpres hg ⟨h15, h14, hks⟩
  have c0 : (s1.callEntry.withRegions [] [⟨b, 4096⟩]).gpr .a0 = b := by rw [g _ (by decide), e0]
  simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr] at h15 h14 hks
  rw [show (s1.callEntry.gpr .a0) = b from c0, u1.mem] at h15 h14 hks
  have ha0 : t.gpr .a0 = b := by rw [hg .a0 (by decide) pow250Fn_a0, e0]
  -- The elements, as the contract reads them.
  have hv : ∀ i : Slot, ∀ {m : Mem}, Proof.X25519.Field32.valAt m b (BitVec.ofNat 32 (offset i)) = V m b (offset i) :=
    fun i m => valAt_ofNat m b i
  refine wp_mv fun t1 v1 => WP.block_nil ⟨⟨⟨fun q hq => ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · by_cases h3 : q = .a3
    · subst h3
      rw [v1.gpr, ha0, hc.a3]
    · rw [v1.other _ h3, hpres q (by revert hq h3; cases q <;> decide), hr1.gpr q (by revert hq; cases q <;> decide)]
  · rw [v1.rd, hrd, u1.rd]
  · rw [v1.wr, hwr, u1.wr]
  · rw [v1.sp, hsp, u1.sp]
  · rw [v1.mem]
    intro x hx
    have hnf := hx _ (List.mem_singleton_self _)
    by_cases hw : (⟨b, 4096⟩ : Region).Contains x 1
    · have hi : (x - b).toNat + 1 ≤ 4096 := hw
      have hx' : x = b + BitVec.ofNat 64 (x - b).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have hlo : (x - b).toNat < 64 ∨ 1024 ≤ (x - b).toNat := by
        by_contra hc
        refine hnf ?_
        rw [hx']
        exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
      rw [hx']
      exact hks _ (by simp only [Proof.X25519.Field32.wsBytes]; omega_arith)
        (by simp only [Proof.X25519.Field32.eAt, Proof.X25519.Field32.ownEnd]; omega_arith)
    · rw [← u1.mem]
      exact hfr x fun r hr => by rw [List.mem_singleton.mp hr]; exact hw
  · rw [v1.mem]
    rw [show Proof.X25519.Field32.oAt = offset 15 from rfl, show Proof.X25519.Field32.aAt = offset 2 from rfl,
      hv, hv] at h15
    exact env_of_val h15
  · rw [v1.mem]
    rw [show Proof.X25519.Field32.eAt = offset 14 from rfl, show Proof.X25519.Field32.aAt = offset 2 from rfl,
      hv, hv] at h14
    exact env_of_val h14
  · intro i hi
    rw [v1.mem]; exact env_keeps₂ hks hi

/-- `sqnLoop o n`: slot `o` squared `n` times. -/
theorem sqnLoop_ok {b : Addr} {s : State} (hc : Ctx b s) (o : Slot) (ho : 14 ≤ o.val) {n : Nat} (hn : 1 ≤ n)
    (hn' : n < 2048) :
    WP isa (sqnLoop o n) s fun t =>
      Rest (.t1 :: clob64) s t ∧ Frame [PR b] s.mem t.mem ∧
      env t.mem b = Function.update (env s.mem b) o (sqn (env s.mem b o) n) := by
  unfold sqnLoop
  refine WP.seq (wp_li (by omega_arith) fun s1 u1 => WP.block_nil ?_)
  refine sqLoop_ok hc o ho (env s.mem b o) n hn' n s1 hn (Nat.le_refl _) (u1.rest (by decide))
    (by rw [u1.mem]; exact Frame.refl _ _) u1.gpr ?_
  rw [u1.mem, Nat.sub_self]
  exact (Function.update_eq_self _ _).symm

theorem inv_exp : (2 ^ 250 - 1) * 2 ^ 5 + 11 = P - 2 := by decide

/-- **The inverse of slot 2**, into slot 15; slots 0–13 kept. -/
theorem invert_ok {b : Addr} {s : State} (hc : Ctx8 b s) :
    WP isa Impl.Ed25519.RISCV64.invert s fun t => Keep b s t ∧
      env t.mem b 15 = Spec.X25519.pow (env s.mem b 2) (P - 2) ∧
      ∀ i : Slot, i.val < 14 → env t.mem b i = env s.mem b i := by
  unfold Impl.Ed25519.RISCV64.invert
  refine WP.seq (WP.mono (power250_ok hc) fun t1 ⟨k1, e15, e14, ek⟩ => ?_)
  have hc1 : Ctx8 b t1 := hc.of_keep k1
  refine WP.seq (WP.mono (sqnLoop_ok hc1.ctx 15 (by decide) (n := 5) (by decide) (by decide))
    fun t2 ⟨r2, f2, e2⟩ => ?_)
  have hc2 : Ctx8 b t2 := hc1.of_rest r2 (by decide)
  refine WP.mono (mulCall_ok hc2.ctx hc2.ws 15 15 14) fun t3 ⟨k3, e3⟩ => ⟨?_, ?_, fun i hi => ?_⟩
  · refine k1.trans (Keep.trans ⟨r2.mono (by decide), f2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩⟩ k3)
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
  · rw [e3, Function.update_self, e2, Function.update_self, Function.update_of_ne (by decide), e15, e14,
      Proof.X25519.sqn_pw, Proof.X25519.pw_mul, inv_exp, Proof.X25519.pow_pw]
  · have h15 : i ≠ 15 := fun h => by subst h; exact absurd hi (by decide)
    rw [e3, Function.update_of_ne h15, e2, Function.update_of_ne h15, ek i hi]

theorem affine_eval (e : Env) :
    evalOps affineOps e 0 = e 0 * e 15 ∧ evalOps affineOps e 1 = e 1 * e 15 := ⟨rfl, rfl⟩

/-- **The affine coordinates** `x = X/Z`, `y = Y/Z` into slots 0 and 1. -/
theorem pointAffine_ok {b : Addr} {s : State} (hc : Ctx8 b s) :
    WP isa pointAffine s fun t => Keep b s t ∧
      env t.mem b 0 = env s.mem b 0 * Spec.X25519.pow (env s.mem b 2) (P - 2) ∧
      env t.mem b 1 = env s.mem b 1 * Spec.X25519.pow (env s.mem b 2) (P - 2) := by
  unfold pointAffine
  refine WP.seq (WP.mono (invert_ok hc) fun t ⟨kt, e15, ek⟩ => ?_)
  refine WP.mono (fieldCode_ok affineOps (hc.of_keep kt).ctx (hc.of_keep kt).ws) fun u ⟨ku, eu⟩ => ⟨kt.trans ku, ?_, ?_⟩
  · rw [eu, (affine_eval _).1, ek 0 (by decide), e15]
  · rw [eu, (affine_eval _).2, ek 1 (by decide), e15]

theorem V_mod2 (m : Mem) (b : Addr) (o : Nat) : V m b o % 2 = limb m b o 0 % 2 := by
  unfold V
  have h : ∀ n, val32 (limb m b o) (n + 1) % 2 = limb m b o 0 % 2 := by
    intro n
    induction n with
    | zero => simp [val32]
    | succ n ih =>
      rw [val32_succ, show 2 ^ (32 * (n + 1)) * limb m b o (n + 1) = 2 * (2 ^ (32 * n + 31) * limb m b o (n + 1)) by
        rw [← Nat.mul_assoc, ← Nat.pow_succ']; congr 2, Nat.add_mul_mod_self_left, ih]
  exact h 7

section
variable {b : Addr}

/-- The parity of the element at `FR` at bit 31 of `t6`. -/
theorem pointSign_ok {s : State} (hc : Ctx b s) :
    WP isa (.block pointSign) s fun t => Rest [.a4, .t6] s t ∧ t.mem = s.mem ∧
      (t.gpr .t6).toNat = (V s.mem b FR % 2) * 2 ^ 31 := by
  have hF := FR_eq
  unfold pointSign
  refine lw0_ok hc (d := FR) (by omega_arith) (by omega_arith) fun s1 u1 => wp_sll (by decide) fun s2 u2 => wp_srl (by decide) fun s3 u3 =>
    WP.block_nil ⟨(u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
      by rw [u3.mem, u2.mem, u1.mem], ?_⟩
  have e7 : (s1.gpr .a4).toNat = limb s.mem b FR 0 := by rw [u1.gpr, toNat_ext32]; rfl
  have hl := limb_lt s.mem b FR 0
  rw [u3.gpr, toNat_shr, u2.gpr, toNat_shl, e7, V_mod2,
    show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, Nat.mul_mod_mul_right,
    show (2 : Nat) ^ 63 = 2 ^ 31 * 2 ^ 32 from rfl, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]

/-- The parity added at bit 255 of the element at `FR`, below `2^255`. -/
theorem encodeSign_ok {s : State} (hc : Ctx b s) {y x : Nat} (hy : y < 2 ^ 255) (hv : V s.mem b FR = y)
    (hs : (s.gpr .t6).toNat = (x % 2) * 2 ^ 31) :
    WP isa (.block encodeSign) s fun t => Rest [.a4] s t ∧ Frame [⟨b + BitVec.ofNat 64 (FR + 28), 4⟩] s.mem t.mem ∧
      V t.mem b FR = y + (x % 2) * 2 ^ 255 := by
  have hF := FR_eq
  have h7 : limb s.mem b FR 7 < 2 ^ 31 := by
    have hv7 : val32 (limb s.mem b FR) 7 + 2 ^ 224 * limb s.mem b FR 7 = y := by rw [← hv]; rfl
    by_contra h
    have : 2 ^ 224 * 2 ^ 31 ≤ 2 ^ 224 * limb s.mem b FR 7 := Nat.mul_le_mul_left _ (by omega)
    omega_arith
  unfold encodeSign
  refine lw0_ok hc (d := FR + 28) (by omega_arith) (by omega_arith) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e2 : (s2.gpr .a4).toNat = limb s.mem b FR 7 + (x % 2) * 2 ^ 31 := by
    have e1 : (s1.gpr .a4).toNat = limb s.mem b FR 7 := by rw [u1.gpr, toNat_ext32]; rfl
    have hx := Nat.mod_lt x (show 0 < 2 by decide)
    rw [u2.gpr, u1.other .t6 (by decide), toNat_add_lt (by rw [e1, hs]; omega_arith), e1, hs]
  have hr2 : Rest [.a4] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  refine sw0_ok (hc.of_rest hr2 (by decide)) (d := FR + 28) (by omega_arith) (by omega_arith) fun s3 u3 => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact hr2.trans (u3.rest _)
  · rw [u3.mem, u2.mem, u1.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := FR + 28) (n := 32 / 8) (Nat.le_refl _) (by omega_arith) (by omega_arith))
  · have hm : s3.mem = s.mem.writeW (b + BitVec.ofNat 64 (FR + 28)) ((s2.gpr .a4).setWidth 32) := by
      rw [u3.mem, u2.mem, u1.mem]
    have hl : ∀ k < 8, limb s3.mem b FR k = if k = 7 then limb s.mem b FR 7 + (x % 2) * 2 ^ 31 else limb s.mem b FR k := by
      intro k hk
      rw [limb, hm]
      by_cases h : k = 7
      · subst h
        have hx := Nat.mod_lt x (show 0 < 2 by decide)
        rw [iteT rfl, wd_write_self, toNat_lo32, e2, Nat.mod_eq_of_lt (by omega_arith)]
      · rw [iteF h, wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; rfl
    rw [V, val32_congr hl, ← hv, V]
    simp only [val32, ite_true, show (0 : Nat) ≠ 7 by decide, show (1 : Nat) ≠ 7 by decide,
      show (2 : Nat) ≠ 7 by decide, show (3 : Nat) ≠ 7 by decide, show (4 : Nat) ≠ 7 by decide,
      show (5 : Nat) ≠ 7 by decide, show (6 : Nat) ≠ 7 by decide, ite_false]
    omega_arith

/-- The number `encodePoint` encodes. -/
def encodeNum (p : Spec.Ed25519.Point) : Nat :=
  (p.Y * Spec.X25519.pow p.Z (P - 2)).val + ((p.X * Spec.X25519.pow p.Z (P - 2)).val % 2) * 2 ^ 255

theorem encodePoint_eq (p : Spec.Ed25519.Point) : Spec.Ed25519.encodePoint p = Spec.Ed25519.encodeLE 32 (encodeNum p) :=
  rfl

theorem env_val (m : Mem) (i : Slot) : (env m b i).val = V m b (offset i) % P := rfl

/-- **The encoding** of the point of slots 0–3, at `FR`. -/
theorem pointEncode_ok {s : State} (hc : Ctx8 b s) :
    WP isa pointEncode s fun t => Rest (.t6 :: fclob) s t ∧ Frame [FA b] s.mem t.mem ∧
      V t.mem b FR = encodeNum (point (env s.mem b) 0 1 2 3) := by
  have hF := FR_eq
  unfold pointEncode
  refine WP.seq (WP.mono (pointAffine_ok hc) fun t1 ⟨k1, e0, e1⟩ => ?_)
  have hc1 : Ctx b t1 := (hc.of_keep k1).ctx
  simp only [List.append_assoc]
  refine WP.append (freeze_ok hc1 0) fun t2 ⟨r2, f2, _, v2⟩ => ?_
  have hc2 : Ctx b t2 := hc1.of_rest r2 (by decide)
  refine WP.append (pointSign_ok hc2) fun t3 ⟨r3, m3, e17⟩ => ?_
  have hc3 : Ctx b t3 := hc2.of_rest r3 (by decide)
  refine WP.append (freeze_ok hc3 1) fun t4 ⟨r4, f4, _, v4⟩ => ?_
  have hc4 : Ctx b t4 := hc3.of_rest r4 (by decide)
  obtain ⟨y, hy⟩ : ∃ y, y = (point (env s.mem b) 0 1 2 3).Y * Spec.X25519.pow (point (env s.mem b) 0 1 2 3).Z (P - 2) :=
    ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = (point (env s.mem b) 0 1 2 3).X * Spec.X25519.pow (point (env s.mem b) 0 1 2 3).Z (P - 2) :=
    ⟨_, rfl⟩
  have hv4 : V t4.mem b FR = y.val := by
    rw [v4, m3, ← env_val, env_keep f2 1 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by simp only [offset]; omega_arith)) (by simp only [offset]; omega_arith) (by omega_arith),
      e1, hy]
    rfl
  have hs4 : (t4.gpr .t6).toNat = (x.val % 2) * 2 ^ 31 := by
    rw [r4.gpr _ (by decide), e17, v2, ← env_val, e0, hx]; rfl
  refine WP.mono (encodeSign_ok hc4 (y := y.val) (x := x.val) (Nat.lt_trans y.isLt (by decide)) hv4 hs4)
    fun t5 ⟨r5, f5, v5⟩ => ⟨?_, ?_, ?_⟩
  · exact (k1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((r4.mono (by decide)).trans (r5.mono (by decide)))))
  · have hs : ∀ d n, d + n ≤ 1024 → 64 ≤ d → ∀ r ∈ ([⟨b + BitVec.ofNat 64 d, n⟩] : List Region),
        ∃ r' ∈ [FA b], r.Sub r' := fun d n h1 h2 r hr =>
      ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩
    refine k1.frame.trans ((f2.sub (hs FR 64 (by omega_arith) (by omega_arith))).trans ?_)
    rw [← m3]
    exact (f4.sub (hs FR 64 (by omega_arith) (by omega_arith))).trans (f5.sub (hs (FR + 28) 4 (by omega_arith) (by omega_arith)))
  · rw [v5, encodeNum, ← hx, ← hy]

end

end VG.Proof.Ed25519.RISCV64

end

end

/-!
# Ed25519 on RISC-V: the candidate `x` of a decoding

`rootPower_ok`: slot 15 is `z^((p - 5) / 8)` for `z` in slot 2, by a call of
`vg_gf25519_r32_pow250`, two squarings and a product. `recoverCandidate_ok`:
from `y` in slot 1, `u = y² - 1` in slot 6, `v = d y² + 1` in slot 7, the
candidate `x = u v³ (u v⁷)^((p - 5) / 8)` (`rootX`) in slot 0, `v x²` in slot
11 and `-u` in slot 12, as `recoverX` computes them.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P)
open VG.Proof.Ed25519 (rootU rootV rootX)

theorem root_exp : (2 ^ 250 - 1) * 2 ^ 2 + 1 = (P - 5) / 8 := by decide

section
variable {b : Addr}

/-- **`z^((p - 5) / 8)`** of slot 2, into slot 15; slots 0–13 kept. -/
theorem rootPower_ok {s : State} (hc : Ctx8 b s) :
    WP isa rootPower s fun t => Keep b s t ∧
      env t.mem b 15 = Spec.X25519.pow (env s.mem b 2) ((P - 5) / 8) ∧
      ∀ i : Slot, i.val < 14 → env t.mem b i = env s.mem b i := by
  unfold Impl.Ed25519.RISCV64.rootPower
  refine WP.seq (WP.mono (power250_ok hc) fun t1 ⟨k1, e15, _, ek⟩ => ?_)
  have hc1 : Ctx8 b t1 := hc.of_keep k1
  refine WP.seq (WP.mono (sqnLoop_ok hc1.ctx 15 (by decide) (n := 2) (by decide) (by decide))
    fun t2 ⟨r2, f2, e2⟩ => ?_)
  have hc2 : Ctx8 b t2 := hc1.of_rest r2 (by decide)
  refine WP.mono (mulCall_ok hc2.ctx hc2.ws 15 15 2) fun t3 ⟨k3, e3⟩ => ⟨?_, ?_, fun i hi => ?_⟩
  · refine k1.trans (Keep.trans ⟨r2.mono (by decide), f2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩⟩ k3)
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_using []) (by omega_using [])
  · have hz : env t1.mem b 2 = env s.mem b 2 := ek 2 (by decide)
    rw [e3, Function.update_self, e2, Function.update_self, Function.update_of_ne (by decide), e15, hz,
      Proof.X25519.sqn_pw]
    conv => lhs; arg 2; rw [← Proof.X25519.pw_one (env s.mem b 2)]
    rw [Proof.X25519.pw_mul, root_exp, Proof.X25519.pow_pw]
  · have h15 : i ≠ 15 := fun h => by subst h; exact absurd hi (by decide)
    rw [e3, Function.update_of_ne h15, e2, Function.update_of_ne h15, ek i hi]

/-- The slots `recoverInitOps` computes from `y` in slot 1. -/
theorem recoverInit_eval (e : Env) :
    evalOps recoverInitOps e 1 = e 1 ∧ evalOps recoverInitOps e 6 = rootU (e 1) ∧
      evalOps recoverInitOps e 7 = rootV (e 1) ∧
      evalOps recoverInitOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
      evalOps recoverInitOps e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 := by
  refine ⟨rfl, rfl, rfl, (Proof.Ed25519.pow_three _ : _ = _), ?_⟩
  rw [← Proof.Ed25519.pow_seven]
  rfl

theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧ evalOps recoverFinishOps e 6 = e 6 ∧
      evalOps recoverFinishOps e 7 = e 7 ∧ evalOps recoverFinishOps e 1 = e 1 ∧
      evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
      evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The candidate**, for `y` in slot 1. -/
theorem recoverCandidate_ok {s : State} (hc : Ctx8 b s) :
    WP isa recoverCandidate s fun t => Keep b s t ∧
      env t.mem b 0 = rootX (env s.mem b 1) ∧ env t.mem b 1 = env s.mem b 1 ∧
      env t.mem b 6 = rootU (env s.mem b 1) ∧ env t.mem b 7 = rootV (env s.mem b 1) ∧
      env t.mem b 11 = rootV (env s.mem b 1) * rootX (env s.mem b 1) * rootX (env s.mem b 1) ∧
      env t.mem b 12 = 0 - rootU (env s.mem b 1) := by
  unfold recoverCandidate
  refine WP.seq (WP.mono (fieldCode_ok _ hc.ctx hc.ws) fun s1 ⟨k1, e1⟩ => ?_)
  obtain ⟨a1, au, av, av3, a2⟩ := recoverInit_eval (env s.mem b)
  rw [← e1] at a1 au av av3 a2
  have hc1 : Ctx8 b s1 := hc.of_keep k1
  refine WP.seq (WP.mono (rootPower_ok hc1) fun s2 ⟨k2, e15, ek⟩ => ?_)
  have hc2 : Ctx8 b s2 := hc1.of_keep k2
  refine WP.mono (fieldCode_ok _ hc2.ctx hc2.ws) fun t ⟨k3, e3⟩ => ?_
  obtain ⟨f0, f6, f7, f1, f11, f12⟩ := recoverFinish_eval (env s2.mem b)
  rw [← e3] at f0 f6 f7 f1 f11 f12
  have bx : env s2.mem b 6 * env s2.mem b 9 * env s2.mem b 15 = rootX (env s.mem b 1) := by
    rw [ek 6 (by decide), ek 9 (by decide), e15, a2, au, av3]
    rfl
  refine ⟨k1.trans (k2.trans k3), by rw [f0, bx], by rw [f1, ek 1 (by decide), a1], ?_, ?_, ?_, ?_⟩
  · rw [f6, ek 6 (by decide), au]
  · rw [f7, ek 7 (by decide), av]
  · rw [f11, bx, ek 7 (by decide), av]
  · rw [f12, ek 6 (by decide), au]

end

end VG.Proof.Ed25519.RISCV64

end

end

/-! ### `Ed25519.RISCV64.FieldTest`, which this module and modules that import it used -/

section

/-!
# Ed25519 on RISCV64: testing elements

`wordsZero o` leaves `a2` zero exactly when the eight words at `o` are
(`wordsZero_ok`), and `wordsEqual a b` exactly when those at `a` and `b`
agree (`wordsEqual_ok`). With `freeze`, `fieldZero a` tests the element of
slot `a` (`fieldZero_ok`), and `fieldEqual a c` whether the elements of
slots `a` and `c` are equal (`fieldEqual_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519
open VG.Spec.X25519 (P)

/-- Limbs below `2³²` are all zero exactly when their value is. -/
theorem val32_eq_zero {f : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 2 ^ 32) :
    val32 f n = 0 ↔ ∀ k < n, f k = 0 := by
  refine ⟨fun h k hk => ?_, fun h => ?_⟩
  · rw [← val32_div hf hk, h, Nat.zero_div, Nat.zero_mod]
  · rw [val32_congr (g := fun _ => 0) h, val32_zero_fn]

/-- Limbs below `2³²` agree exactly when their values do. -/
theorem val32_eq_iff {f g : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 2 ^ 32) (hg : ∀ k < n, g k < 2 ^ 32) :
    val32 f n = val32 g n ↔ ∀ k < n, f k = g k := by
  refine ⟨fun h k hk => ?_, val32_congr⟩
  rw [← val32_div hf hk, h, val32_div hg hk]

/-- The sum of the first `k` values of `f`. -/
def psum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => psum f k + f k

theorem psum_le {f : Nat → Nat} (hf : ∀ k, f k < 2 ^ 32) : ∀ k, psum f k ≤ k * 2 ^ 32
  | 0 => Nat.le_refl _
  | k + 1 => by
    have := psum_le hf k
    have := hf k
    simp only [psum, Nat.succ_mul]
    omega_arith

theorem psum_eq_zero {f : Nat → Nat} : ∀ {k : Nat}, psum f k = 0 ↔ ∀ j < k, f j = 0
  | 0 => by simp [psum]
  | k + 1 => by
    rw [psum, Nat.add_eq_zero_iff, psum_eq_zero]
    exact ⟨fun ⟨h1, h2⟩ j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      exacts [h1 j hj, h2], fun h => ⟨fun j hj => h j (by omega_using [hj]), h k (by omega_using [])⟩⟩

section
variable {b : Addr}

theorem wordsZero_ok {s : State} (hc : Ctx b s) {o : Nat} (ho : o + 32 ≤ 2048) (ho4 : o % 4 = 0) :
    WP isa (.block (wordsZero o)) s fun t =>
      Rest [.a2, .a4] s t ∧ t.mem = s.mem ∧ (t.gpr .a2 = 0 ↔ V s.mem b o = 0) := by
  unfold wordsZero
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8)
    (fun k t => Rest [.a2, .a4] s t ∧ t.mem = s.mem ∧ (t.gpr .a2).toNat = psum (limb s.mem b o) k)
    (fun k t hk ⟨hr, hm, h5⟩ => ?_) 8 (Nat.le_refl _) s1
    ⟨u1.rest (by decide), u1.mem, by rw [u1.gpr]; rfl⟩) fun t ⟨hr, hm, h5⟩ => ⟨hr, hm, ?_⟩
  · have ht : Ctx b t := hc.of_rest hr (by decide)
    unfold sumLimb
    refine lw0_ok ht (d := o + 4 * k) (by omega_using [ho, hk]) (by omega_using [ho4]) fun s2 u2 => wp_add fun s3 u3 => WP.block_nil ⟨?_, ?_, ?_⟩
    · exact hr.trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
    · rw [u3.mem, u2.mem, hm]
    · have hle := psum_le (fun j => limb_lt s.mem b o j) k
      have hl := limb_lt s.mem b o k
      have e7 : (s2.gpr .a4).toNat = limb s.mem b o k := by rw [u2.gpr, toNat_ext32, hm]; rfl
      rw [u3.gpr, u2.other _ (by decide), toNat_add_lt (by rw [h5, e7]; omega_using [hk, hle, hl]), h5, e7]
      rfl
  · have hz : t.gpr .a2 = 0 ↔ (t.gpr .a2).toNat = 0 :=
      ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
    rw [hz, h5, psum_eq_zero, V, val32_eq_zero fun k _ => limb_lt _ _ _ _]

theorem wordsEqual_ok {s : State} (hc : Ctx b s) {a c : Nat} (ha : a + 32 ≤ 2048) (hc' : c + 32 ≤ 2048)
    (ha4 : a % 4 = 0) (hc4 : c % 4 = 0) :
    WP isa (.block (wordsEqual a c)) s fun t =>
      Rest [.a2, .a4, .a5] s t ∧ t.mem = s.mem ∧ (t.gpr .a2 = 0 ↔ V s.mem b a = V s.mem b c) := by
  unfold wordsEqual
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8)
    (fun k t => Rest [.a2, .a4, .a5] s t ∧ t.mem = s.mem ∧
      (t.gpr .a2 = 0 ↔ ∀ j < k, limb s.mem b a j = limb s.mem b c j))
    (fun k t hk ⟨hr, hm, h5⟩ => ?_) 8 (Nat.le_refl _) s1
    ⟨u1.rest (by decide), u1.mem, by rw [u1.gpr]; exact ⟨fun _ j hj => absurd hj (by omega_using []), fun _ => rfl⟩⟩)
    fun t ⟨hr, hm, h5⟩ => ⟨hr, hm, ?_⟩
  · have ht : Ctx b t := hc.of_rest hr (by decide)
    unfold equalLimb
    refine lw0_ok ht (d := a + 4 * k) (by omega_using [ha, hk]) (by omega_using [ha4]) fun s2 u2 => ?_
    have hc2 : Ctx b s2 := ht.of_rest (u2.rest (ws := [.a4]) (by decide)) (by decide)
    refine lw0_ok hc2 (d := c + 4 * k) (by omega_using [hc', hk]) (by omega_using [hc4]) fun s3 u3 => wp_xor fun s4 u4 => wp_or fun s5 u5 =>
      WP.block_nil ⟨?_, ?_, ?_⟩
    · exact hr.trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
        ((u4.rest (by decide)).trans (u5.rest (by decide)))))
    · rw [u5.mem, u4.mem, u3.mem, u2.mem, hm]
    · have m2 : s2.mem = s.mem := by rw [u2.mem, hm]
      have or0 : ∀ x y : BitVec 64, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
      have xor0 : ∀ x y : BitVec 64, x ^^^ y = 0 ↔ x = y := fun _ _ => BitVec.xor_eq_zero_iff
      rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u4.gpr,
        u3.other _ (by decide), u2.gpr, u3.gpr, m2, hm, or0, xor0, h5]
      have e : ∀ x y : BitVec 32, x.setWidth 64 = y.setWidth 64 ↔ x.toNat = y.toNat := fun x y =>
        ⟨fun h => by rw [← toNat_ext32 x, ← toNat_ext32 y, h], fun h => by
          apply BitVec.eq_of_toNat_eq; rw [toNat_ext32, toNat_ext32, h]⟩
      rw [e]
      refine ⟨fun ⟨h1, h2⟩ j hj => ?_, fun h => ⟨fun j hj => h j (by omega_using [hj]), h k (by omega_using [])⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      exacts [h1 j hj, h2]
  · rw [h5, V, V, val32_eq_iff (fun k _ => limb_lt _ _ _ _) (fun k _ => limb_lt _ _ _ _)]

theorem fieldZero_ok {s : State} (hc : Ctx b s) (a : Slot) :
    WP isa (fieldZero a) s fun t =>
      Rest [.a1, .a2, .a4, .a5, .t0] s t ∧ Frame [⟨b + BitVec.ofNat 64 FR, 64⟩] s.mem t.mem ∧
      (t.gpr .a2 = 0 ↔ V s.mem b (offset a) % P = 0) := by
  have hX := FR_eq
  unfold fieldZero
  refine WP.seq (WP.mono (freeze_ok hc a) fun s1 ⟨r1, f1, _, v1⟩ => ?_)
  refine WP.mono (wordsZero_ok (hc.of_rest r1 (by decide)) (o := FR) (by omega_using [hX]) (by omega_using [hX])) fun t ⟨r2, m2, h2⟩ =>
    ⟨r1.trans (r2.mono (by decide)), (by rw [m2]; exact f1), (by rw [h2, v1])⟩

theorem fe_sub_eq_zero (x y : Spec.X25519.Fe) : x - y = 0 ↔ x = y := by
  rw [Fin.ext_iff, Fin.ext_iff, Fin.sub_def]
  have hx := x.isLt
  have hy := y.isLt
  show (P - y.val + x.val) % P = 0 ↔ _
  by_cases hxy : y.val ≤ x.val
  · rw [show P - y.val + x.val = (x.val - y.val) + P by omega_using [hxy], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [])]
    omega_using [hxy]
  · rw [Nat.mod_eq_of_lt (by omega_using [hxy])]; omega_using [hxy]

theorem fieldEqual_ok {s : State} (hc : Ctx b s) (hw : WS b s) (a c : Slot) :
    WP isa (fieldEqual a c) s fun t =>
      Keep b s t ∧ env t.mem b = evalOps [.sub 21 a c] (env s.mem b) ∧
      (t.gpr .a2 = 0 ↔ env s.mem b a = env s.mem b c) := by
  have hX := FR_eq
  unfold fieldEqual
  refine WP.seq (WP.mono (fieldCode_ok _ hc hw) fun s1 ⟨k1, e1⟩ => ?_)
  refine WP.mono (fieldZero_ok (k1.ctx hc) 21) fun t ⟨r2, f2, h2⟩ => ⟨⟨k1.rest.trans (r2.mono (by decide)),
    k1.frame.trans (f2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_using [hX]) (by omega_using [hX])⟩)⟩, ?_, ?_⟩
  · have ek : env t.mem b = env s1.mem b := funext fun i => env_keep f2 i fun r hr => by
      have := slot_range i
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX, this])) (by omega_using [this]) (by omega_using [hX])
    rw [ek, e1]
  · have e21 : env s1.mem b 21 = env s.mem b a - env s.mem b c := by
      rw [e1]; simp only [evalOps, List.foldl, evalOp, Function.update_self]
    rw [h2, ← fe_sub_eq_zero, ← e21, Fin.ext_iff]
    rfl

end

end VG.Proof.Ed25519.RISCV64

end

end

/-! ### `Ed25519.RISCV64.RecoverSign`, which this module and modules that import it used -/

section

/-!
# Ed25519 on RISC-V: the sign and the checks of a decoding

A decoding's result is `s3`, 1 for a point (in slots 0–3) and 0 for none
(`DecodeResult`), and it writes `fclob`, `s3` and the field area (`DKeep`).
The sign it took from the encoding is the word at `SIGN` (`SignAt`).
`recoverSign_ok`: from the candidate `x` in slot 0, `signResult`;
`recoverPoint_ok`: the checks of `v x²`, as `recoverResult`, which is the
spec's `recoverX` (`recoverResult_spec`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519 (val32_div)
open VG.Spec.X25519 (P)
open VG.Proof.Ed25519 (rootU rootV rootX recoveredPoint signedX signResult recoverResult)

/-- What a decoding writes. -/
structure DKeep (b : Addr) (s t : State) : Prop where
  rest : Rest (.s3 :: fclob) s t
  frame : Frame [FA b] s.mem t.mem

theorem DKeep.of_keep {b : Addr} {s t : State} (h : Keep b s t) : DKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩

theorem DKeep.trans {b : Addr} {s t u : State} (h : DKeep b s t) (k : DKeep b t u) : DKeep b s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

/-- The result of a decoding. -/
def DecodeResult (b : Addr) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .s3 = 0
  | some p => s.gpr .s3 = 1 ∧ point (env s.mem b) 0 1 2 3 = p

/-- The sign of the encoding, at `SIGN`. -/
def SignAt (b : Addr) (sg : Bool) (m : Mem) : Prop :=
  (m.readW (b + BitVec.ofNat 64 SIGN) 32).setWidth 64 = BitVec.ofNat 64 sg.toNat

theorem SignAt.frame {b : Addr} {sg : Bool} {m m' : Mem} (h : SignAt b sg m) (hf : Frame [FA b] m m') :
    SignAt b sg m' := by
  have hS : SIGN = 24 := rfl
  unfold SignAt
  rw [hf.readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hS])) (by omega_using [hS]) (by omega_using [])) (by decide)]
  exact h

section
variable {b : Addr}

theorem frame_FR {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 FR, 64⟩] m m') : Frame [FA b] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub b (by decide) (by decide)⟩

theorem env_FR {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 FR, 64⟩] m m') : env m' b = env m b :=
  funext fun i => env_keep hf i fun r hr => by
    have := slot_range i
    have hX : FR = 864 := rfl
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [this, hX])) (by omega_using [this]) (by omega_using [hX])

theorem recoverInvalid_ok (s : State) :
    WP isa recoverInvalid s fun t => DKeep b s t ∧ t.mem = s.mem ∧ DecodeResult b none t :=
  wp_li (by decide) fun t u => WP.block_nil ⟨⟨u.rest (by decide), by rw [u.mem]; exact Frame.refl _ _⟩, u.mem,
    show t.gpr .s3 = 0 by rw [u.gpr]; rfl⟩

theorem recoverSuccess_ok {s : State} (hc : Ctx8 b s) :
    WP isa recoverSuccess s fun t => DKeep b s t ∧
      DecodeResult b (some (recoveredPoint (env s.mem b 0) (env s.mem b 1))) t := by
  unfold recoverSuccess
  refine WP.seq (WP.mono (fieldCode_ok _ hc.ctx hc.ws) fun s1 ⟨k1, e1⟩ => ?_)
  refine wp_li (by decide) fun t u => WP.block_nil ⟨(DKeep.of_keep k1).trans
    ⟨u.rest (by decide), by rw [u.mem]; exact Frame.refl _ _⟩, u.gpr, ?_⟩
  rw [u.mem, e1]
  rfl

/-- A residue's parity is its low limb's. -/
theorem V_mod2' (m : Mem) (o : Nat) : V m b o % 2 = limb m b o 0 % 2 := by
  have h := val32_div (r := limb m b o) (n := 8) (fun k _ => limb_lt _ _ _ _) (k := 0) (by decide)
  rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h
  rw [V, ← h, Nat.mod_mod_of_dvd _ (by decide)]

theorem parity_ok {s : State} (hc : Ctx b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa (.block recoverParity) s fun t =>
      Rest [.a2, .a4, .a5] s t ∧ t.mem = s.mem ∧ (t.gpr .a2 = 0 ↔ limb s.mem b FR 0 % 2 = sg.toNat) := by
  unfold recoverParity
  refine lw0_ok hc (d := FR) (by decide) (by decide) fun s1 u1 => wp_sll (by decide) fun s2 u2 => wp_srl (by decide) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc.of_rest ((u1.rest (ws := [.a4]) (by decide)).trans ((u2.rest (by decide)).trans
    (u3.rest (by decide)))) (by decide)
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine lw0_ok hc3 (d := SIGN) (by decide) (by decide) fun s4 u4 => wp_xor fun s5 u5 => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  · rw [u5.mem, u4.mem, m3]
  · have e7 : (s4.gpr .a4).toNat = limb s.mem b FR 0 % 2 := by
      have hb := bit_shift (s1.gpr .a4) (j := 0) (by decide)
      rw [Nat.sub_zero, Nat.shiftRight_zero, Nat.and_one_is_mod] at hb
      rw [u4.other _ (by decide), u3.gpr, u2.gpr, hb, u1.gpr, toNat_ext32]
      rfl
    have e8 : s4.gpr .a5 = BitVec.ofNat 64 sg.toNat := by rw [u4.gpr, m3]; exact hs
    have xor0 : ∀ x y : BitVec 64, x ^^^ y = 0 ↔ x = y := fun _ _ => BitVec.xor_eq_zero_iff
    rw [u5.gpr, xor0, ← BitVec.toNat_inj, e7, e8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := sg.toNat) (by cases sg <;> decide)]

theorem sign_iff (v : Nat) (sg : Bool) : (((v % 2 == 1) == sg) = true) ↔ v % 2 = sg.toNat := by
  have := Nat.mod_lt v (show 0 < 2 by decide)
  cases sg <;> simp <;> omega

/-- The reduced `x`'s parity against the sign: `a2` zero exactly when they match. -/
theorem adjParity_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa (.block (freeze 0 ++ recoverParity)) s fun t => DKeep b s t ∧ env t.mem b = env s.mem b ∧
      (t.gpr .a2 = 0 ↔ (((env s.mem b 0).val % 2 == 1) == sg) = true) := by
  refine WP.append (freeze_ok hc.ctx 0) fun s1 ⟨r1, f1, _, v1⟩ => ?_
  have hc1 : Ctx b s1 := hc.ctx.of_rest r1 (by decide)
  refine WP.mono (parity_ok hc1 (hs.frame (frame_FR f1))) fun s2 ⟨r2, m2, h2⟩ =>
    ⟨⟨r1.trans (r2.mono (by decide)) |>.mono (by decide), by rw [m2]; exact frame_FR f1⟩,
      by rw [m2, env_FR f1], ?_⟩
  have hp : limb s1.mem b FR 0 % 2 = (env s.mem b 0).val % 2 := by
    rw [← V_mod2', v1]; rfl
  rw [hp, ← sign_iff] at h2
  exact h2

/-- **The sign applied**, and the point. -/
theorem recoverAdjust_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa recoverAdjustSign s fun t => DKeep b s t ∧
      DecodeResult b (some (recoveredPoint (signedX (env s.mem b 0) sg) (env s.mem b 1))) t := by
  unfold recoverAdjustSign
  refine WP.seq (WP.mono (adjParity_ok hc hs) fun s2 ⟨hk2, he2, h2⟩ => ?_)
  have hc2 : Ctx8 b s2 := hc.of_rest hk2.rest (by decide)
  refine WP.seq (WP.ite (s2.gpr .a2 == 0) (eval_zero s2 .a2) (fun h => ?_) (fun h => ?_))
  · refine WP.block_nil (WP.mono (recoverSuccess_ok hc2) fun t ⟨kt, dt⟩ => ⟨hk2.trans kt, ?_⟩)
    have hsg : signedX (env s.mem b 0) sg = env s.mem b 0 := by
      unfold signedX; rw [iteT (h2.mp (beq_iff_eq.mp h))]
    rw [hsg, ← he2]; exact dt
  · refine WP.mono (fieldCode_ok _ hc2.ctx hc2.ws) fun s3 ⟨k3, e3⟩ => ?_
    refine WP.mono (recoverSuccess_ok (hc2.of_keep k3)) fun t ⟨kt, dt⟩ => ⟨hk2.trans ((DKeep.of_keep k3).trans kt), ?_⟩
    have hsg : signedX (env s.mem b 0) sg = 0 - env s.mem b 0 := by
      unfold signedX
      exact iteF fun hq => absurd (beq_iff_eq.mpr (h2.mpr hq)) (by simpa using h)
    have hx : env s3.mem b 0 = 0 - env s.mem b 0 := by rw [e3, he2]; rfl
    have hy : env s3.mem b 1 = env s.mem b 1 := by rw [e3, he2]; rfl
    rw [hsg]; rw [hx, hy] at dt; exact dt

/-- **The sign**, for the candidate in slot 0 and `y` in slot 1. -/
theorem recoverSign_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa recoverSign s fun t => DKeep b s t ∧
      DecodeResult b (signResult (env s.mem b 0) (env s.mem b 1) sg) t := by
  unfold recoverSign
  refine WP.seq (WP.mono (fieldZero_ok hc.ctx 0) fun s1 ⟨r1, f1, h1⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest r1 (by decide)
  have he1 : env s1.mem b = env s.mem b := env_FR f1
  have hk1 : DKeep b s s1 := ⟨r1.mono (by decide), frame_FR f1⟩
  have hs1 : SignAt b sg s1.mem := hs.frame (frame_FR f1)
  have hz : (env s.mem b 0 = 0) ↔ V s.mem b (offset 0) % P = 0 := by
    rw [Fin.ext_iff]; exact Iff.rfl
  rw [← hz] at h1
  have adj : WP isa recoverAdjustSign s1 fun t => DKeep b s t ∧
      DecodeResult b (some (recoveredPoint (signedX (env s.mem b 0) sg) (env s.mem b 1))) t :=
    WP.mono (recoverAdjust_ok hc1 hs1) fun t ⟨kt, dt⟩ => ⟨hk1.trans kt, by rw [he1] at dt; exact dt⟩
  refine WP.ite (s1.gpr .a2 == 0) (eval_zero s1 .a2) (fun h => ?_) (fun h => ?_)
  · have hx : env s.mem b 0 = 0 := h1.mp (beq_iff_eq.mp h)
    unfold signTest
    refine WP.seq (lw0_ok hc1.ctx (d := SIGN) (by decide) (by decide) fun s2 u2 => WP.block_nil ?_)
    have e5 : s2.gpr .a2 = BitVec.ofNat 64 sg.toNat := by rw [u2.gpr]; exact hs1
    have hc2 : Ctx8 b s2 := hc1.of_rest (u2.rest (ws := [.a2]) (by decide)) (by decide)
    have hk2 : DKeep b s1 s2 := ⟨u2.rest (by decide), by rw [u2.mem]; exact Frame.refl _ _⟩
    refine WP.ite (s2.gpr .a2 != 0) (eval_nonzero s2 .a2) (fun h' => ?_) (fun h' => ?_)
    · have hsg : sg = true := by
        cases sg with
        | false => rw [e5] at h'; exact absurd h' (by decide)
        | true => rfl
      refine WP.mono (recoverInvalid_ok s2) fun t ⟨kt, _, dt⟩ => ⟨hk1.trans (hk2.trans kt), ?_⟩
      unfold signResult; rw [hx, hsg]; exact dt
    · have hsg : sg = false := by
        cases sg with
        | false => rfl
        | true => rw [e5] at h'; exact absurd h' (by decide)
      refine WP.mono (recoverAdjust_ok hc2 (sg := sg) (by rw [u2.mem]; exact hs1)) fun t ⟨kt, dt⟩ =>
        ⟨hk1.trans (hk2.trans kt), ?_⟩
      have e2 : env s2.mem b = env s.mem b := by rw [u2.mem, he1]
      rw [e2] at dt
      subst hsg
      unfold signResult; rw [iteF (by simp)]; exact dt
  · refine WP.mono adj fun t ⟨kt, dt⟩ => ⟨kt, ?_⟩
    have hx : ¬ env s.mem b 0 = 0 := fun hx => absurd (beq_iff_eq.mpr (h1.mpr hx)) (by simpa using h)
    unfold signResult; rw [iteF (by simp [hx])]; exact dt

/-- **A candidate checked**, for `y` in slot 1: `recoverResult`. -/
theorem recoverPoint_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa recoverPoint s fun t => DKeep b s t ∧ DecodeResult b (recoverResult (env s.mem b 1) sg) t := by
  unfold recoverPoint
  refine WP.seq (WP.mono (recoverCandidate_ok hc) fun a ⟨ka, ax, ay, au, _, avx, anu⟩ => ?_)
  have hca : Ctx8 b a := hc.of_keep ka
  refine WP.seq (WP.mono (fieldEqual_ok hca.ctx hca.ws 11 6) fun c ⟨kc, ec, hc5⟩ => ?_)
  have hcc : Ctx8 b c := hca.of_keep kc
  have hkc : DKeep b s c := DKeep.of_keep (ka.trans kc)
  have hsc : SignAt b sg c.mem := hs.frame (ka.trans kc).frame
  have cx : env c.mem b 0 = rootX (env s.mem b 1) := by rw [ec, ← ax]; rfl
  have cy : env c.mem b 1 = env s.mem b 1 := by rw [ec, ← ay]; rfl
  rw [avx, au] at hc5
  refine WP.ite (c.gpr .a2 == 0) (eval_zero c .a2) (fun h => ?_) (fun h => ?_)
  · refine WP.mono (recoverSign_ok hcc hsc) fun t ⟨kt, dt⟩ => ⟨hkc.trans kt, ?_⟩
    unfold recoverResult; rw [iteT (hc5.mp (beq_iff_eq.mp h))]
    rw [cx, cy] at dt; exact dt
  · have hne : ¬ rootV (env s.mem b 1) * rootX (env s.mem b 1) * rootX (env s.mem b 1) = rootU (env s.mem b 1) :=
      fun he => absurd (beq_iff_eq.mpr (hc5.mpr he)) (by simpa using h)
    refine WP.seq (WP.mono (fieldEqual_ok hcc.ctx hcc.ws 11 12) fun d ⟨kd, ed, hd5⟩ => ?_)
    have hcd : Ctx8 b d := hcc.of_keep kd
    have hkd : DKeep b s d := hkc.trans (DKeep.of_keep kd)
    have hsd : SignAt b sg d.mem := hsc.frame kd.frame
    have c11 : env c.mem b 11 = env a.mem b 11 := by rw [ec]; rfl
    have c12 : env c.mem b 12 = env a.mem b 12 := by rw [ec]; rfl
    rw [c11, c12, avx, anu] at hd5
    refine WP.ite (d.gpr .a2 == 0) (eval_zero d .a2) (fun h' => ?_) (fun h' => ?_)
    · refine WP.seq (WP.mono (fieldCode_ok _ hcd.ctx hcd.ws) fun f ⟨kf, ef⟩ => ?_)
      refine WP.mono (recoverSign_ok (hcd.of_keep kf) (hsd.frame kf.frame)) fun t ⟨kt, dt⟩ =>
        ⟨hkd.trans ((DKeep.of_keep kf).trans kt), ?_⟩
      have fx : env f.mem b 0 = rootX (env s.mem b 1) * Spec.Ed25519.sqrtM1 := by
        rw [ef, ← cx, show env c.mem b 0 = env d.mem b 0 by rw [ed]; rfl]; rfl
      have fy : env f.mem b 1 = env s.mem b 1 := by
        rw [ef, ← cy, show env c.mem b 1 = env d.mem b 1 by rw [ed]; rfl]; rfl
      unfold recoverResult; rw [iteF hne, iteT (hd5.mp (beq_iff_eq.mp h'))]
      rw [fx, fy] at dt; exact dt
    · have hne' : ¬ rootV (env s.mem b 1) * rootX (env s.mem b 1) * rootX (env s.mem b 1) =
          0 - rootU (env s.mem b 1) :=
        fun he => absurd (beq_iff_eq.mpr (hd5.mpr he)) (by simpa using h')
      refine WP.mono (recoverInvalid_ok d) fun t ⟨kt, _, dt⟩ => ⟨hkd.trans kt, ?_⟩
      unfold recoverResult; rw [iteF hne, iteF hne']; exact dt

end

end VG.Proof.Ed25519.RISCV64

end

end

/-!
# Ed25519 on RISC-V: decoding a point

`pointDecode` with the encoding at `s0`: its words into slot 1, bit 255
split off to `SIGN` (`split_ok`), `y` canonical (`pointDecodeLoad_ok`), and
the recovery of `x` (`recoverPoint_ok`): `decodePoint` of the 32 bytes
(`pointDecode_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519 (val32_succ val32_lt val32_congr)
open VG.Spec.X25519 (P)
open VG.Spec.Ed25519 (decodeLE bytesAt)

/-- What a decoding writes, with its sign. -/
structure DecKeep (b : Addr) (s t : State) : Prop where
  rest : Rest (.s3 :: fclob) s t
  frame : Frame [⟨b + BitVec.ofNat 64 SIGN, 4⟩, FA b] s.mem t.mem

theorem DecKeep.trans {b : Addr} {s t u : State} (h : DecKeep b s t) (k : DecKeep b t u) : DecKeep b s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem DecKeep.of_dkeep {b : Addr} {s t : State} (h : DKeep b s t) : DecKeep b s t :=
  ⟨h.rest, h.frame.mono (by simp)⟩

theorem toNat_beq_one {x : Nat} (h : x < 2) : (x == 1).toNat = x := by
  rcases (by omega_arith : x = 0 ∨ x = 1) with rfl | rfl <;> rfl

section
variable {b : Addr}

/-- **Bit 255 of slot 1**, to `SIGN`, and cleared. -/
theorem split_ok {s : State} (hc : Ctx b s) :
    WP isa (.block splitYSign) s fun t =>
      Rest [.a4, .a5] s t ∧
      Frame [⟨b + BitVec.ofNat 64 SIGN, 4⟩, ⟨b + BitVec.ofNat 64 (offset 1 + 28), 4⟩] s.mem t.mem ∧
      SignAt b (limb s.mem b (offset 1) 7 / 2 ^ 31 == 1) t.mem ∧
      limb t.mem b (offset 1) 7 = limb s.mem b (offset 1) 7 % 2 ^ 31 ∧
      ∀ j < 7, limb t.mem b (offset 1) j = limb s.mem b (offset 1) j := by
  have hS : SIGN = 24 := rfl
  have h1 : offset 1 = 96 := rfl
  unfold splitYSign VG.Impl.X25519.RISCV64.low31
  simp only [List.cons_append, List.nil_append]
  refine lw0_ok hc (d := offset 1 + 28) (by decide) (by decide) fun s2 u2 => wp_srl (by decide) fun s3 u3 => ?_
  have hr3 : Rest [.a4, .a5] s s3 := (u2.rest (by decide)).trans (u3.rest (by decide))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  refine sw0_ok hc3 (d := SIGN) (by decide) (by decide) fun s4 u4 => ?_
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest []) (by decide)
  refine wp_sll (by decide) fun s5 u5 => wp_srl (by decide) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := hc4.of_rest ((u5.rest (ws := [.a4]) (by decide)).trans (u6.rest (by decide))) (by decide)
  refine sw0_ok hc6 (d := offset 1 + 28) (by decide) (by decide) fun s7 u7 => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hr3.trans ((u4.rest _).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest _))))
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem]
    refine Frame.writeW (Frame.writeW (Frame.refl _ _) List.mem_cons_self _ ?_)
      (List.mem_cons_of_mem _ List.mem_cons_self) _ ?_ <;> exact Region.contains_self _ _
  · have hw : (s2.gpr .a4).toNat = limb s.mem b (offset 1) 7 := by rw [u2.gpr, toNat_ext32]; rfl
    have hx : limb s.mem b (offset 1) 7 / 2 ^ 31 < 2 := by have := limb_lt s.mem b (offset 1) 7; omega_arith
    unfold SignAt
    rw [u7.mem, Mem.readW_writeW_sep (Offset.sep b (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), u6.mem,
      u5.mem, u4.mem, Mem.readW_writeW_self32]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_ext32, toNat_lo32, u3.gpr, toNat_shr, hw, BitVec.toNat_ofNat, toNat_beq_one hx, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  · show wd s7.mem b (offset 1 + 28) = _
    rw [u7.mem, wd_write_self, toNat_lo32, u6.gpr, u5.gpr, low31_val, u4.gpr, u3.other _ (by decide), u2.gpr,
      toNat_ext32]
    show (s.mem.readW (b + BitVec.ofNat 64 (offset 1 + 28)) 32).toNat % 2 ^ 31 % 2 ^ 32 = _
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
    rfl
  · intro j hj
    show wd s7.mem b (offset 1 + 4 * j) = wd s.mem b (offset 1 + 4 * j)
    rw [u7.mem, wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), u6.mem, u5.mem, u4.mem, wd,
      Mem.readW_writeW_sep (Offset.sep b (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), u3.mem, u2.mem]
    rfl

/-- **The encoding loaded**: `y` (bit 255 cleared) in slot 1, the sign at `SIGN`, and `a2` zero exactly
when `y < p`. -/
theorem pointDecodeLoad_ok {s : State} (hc : Ctx8 b s) {q : Addr} (h14 : s.gpr .s0 = q)
    (hr : ∀ k < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (0 + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 (offset 1), 32⟩) :
    WP isa pointDecodeLoad s fun t => DecKeep b s t ∧
      SignAt b (decodeLE (bytesAt s.mem q 32) / 2 ^ 255 == 1) t.mem ∧
      env t.mem b 1 = Proof.X25519.toFe (decodeLE (bytesAt s.mem q 32) % 2 ^ 255) ∧
      (t.gpr .a2 = 0 ↔ decodeLE (bytesAt s.mem q 32) % 2 ^ 255 < P) := by
  have h1 : offset 1 = 96 := rfl
  have hX := FR_eq
  unfold pointDecodeLoad canonicalY
  refine WP.seq (WP.append (unpackField_ok hc.ctx (by decide) h14 (o := offset 1) (src := 0) (by decide) (by decide) (by decide) hr hd)
    fun s1 ⟨r1, f1, l1⟩ => ?_)
  have hn : decodeLE (bytesAt s.mem q 32) = V s1.mem b (offset 1) :=
    bytes_of_words fun j hj => by rw [l1 j hj, Nat.zero_add]
  have hc1 : Ctx b s1 := hc.ctx.of_rest r1 (by decide)
  refine WP.mono (split_ok hc1) fun s2 ⟨r2, f2, sg2, l7, lj⟩ => ?_
  -- `y`, and the sign, from the top limb.
  have hv1 := val32_succ (limb s1.mem b (offset 1)) 7
  have hv2 := val32_succ (limb s2.mem b (offset 1)) 7
  have hA := val32_lt (f := limb s1.mem b (offset 1)) (n := 7) fun k _ => limb_lt _ _ _ _
  have hL := limb_lt s1.mem b (offset 1) 7
  rw [val32_congr lj, l7] at hv2
  rw [show (2 : Nat) ^ (32 * 7) = 2 ^ 224 from rfl] at hv1 hv2 hA
  have hy : V s2.mem b (offset 1) = decodeLE (bytesAt s.mem q 32) % 2 ^ 255 := by
    rw [hn, V, V, hv1, hv2]; omega_arith
  have hsg : decodeLE (bytesAt s.mem q 32) / 2 ^ 255 = limb s1.mem b (offset 1) 7 / 2 ^ 31 := by
    rw [hn, V, hv1]; omega_arith
  rw [← hsg] at sg2
  have r12 : Rest [.a4, .a5] s s2 := (r1.mono (by decide)).trans r2
  have hc2 : Ctx8 b s2 := hc.of_rest r12 (by decide)
  have hF2 : Frame [⟨b + BitVec.ofNat 64 SIGN, 4⟩, FA b] s.mem s2.mem := by
    refine (f1.sub fun r hr => ⟨FA b, by simp, ?_⟩).trans (f2.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_arith) (by omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨FA b, by simp, Offset.sub b (by omega_arith) (by omega_arith)⟩
  -- `y` canonical.
  refine WP.seq (WP.mono (freeze_ok hc2.ctx 1) fun s3 ⟨r3, f3, _, v3⟩ => ?_)
  have hc3 : Ctx b s3 := hc2.ctx.of_rest r3 (by decide)
  refine WP.mono (wordsEqual_ok hc3 (a := offset 1) (c := FR) (by decide) (by decide) (by decide) (by decide)) fun t ⟨r4, m4, h4⟩ => ?_
  have hs3 : V s3.mem b (offset 1) = V s2.mem b (offset 1) := by
    unfold V
    exact val32_congr (limb_frame f3 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
  refine ⟨⟨(r12.mono (by decide)).trans ((r3.mono (by decide)).trans (r4.mono (by decide))),
    hF2.trans (by rw [m4]; exact (frame_FR f3).mono (by simp))⟩, ?_, ?_, ?_⟩
  · rw [m4]; exact sg2.frame (frame_FR f3)
  · rw [m4, ← hy, ← hs3]; rfl
  · rw [h4, hs3, v3, hy]
    generalize decodeLE (bytesAt s.mem q 32) % 2 ^ 255 = y
    rw [eq_comm, Nat.mod_eq_iff_lt (by decide)]

/-- **A point decoded**, from the 32 bytes at `s0`. -/
theorem pointDecode_ok {s : State} (hc : Ctx8 b s) {q : Addr} (h14 : s.gpr .s0 = q)
    (hr : ∀ k < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (0 + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 (offset 1), 32⟩) :
    WP isa pointDecode s fun t => DecKeep b s t ∧
      ∃ o, Spec.Ed25519.decodePoint (bytesAt s.mem q 32) = o ∧ DecodeResult b o t := by
  have hl : (bytesAt s.mem q 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  rw [Proof.Ed25519.decodePoint32 _ hl]
  unfold pointDecode
  refine WP.seq (WP.mono (pointDecodeLoad_ok hc h14 hr hd) fun s1 ⟨k1, sg1, y1, h5⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest k1.rest (by decide)
  refine WP.ite (s1.gpr .a2 == 0) (eval_zero s1 .a2) (fun h => ?_) (fun h => ?_)
  · have hy := h5.mp (beq_iff_eq.mp h)
    refine WP.mono (recoverPoint_ok hc1 sg1) fun t ⟨kt, dt⟩ => ⟨k1.trans (DecKeep.of_dkeep kt), _, ?_, dt⟩
    rw [iteT hy, Proof.Ed25519.recoverResult_spec, y1]; rfl
  · have hy : ¬ decodeLE (bytesAt s.mem q 32) % 2 ^ 255 < P := fun hy =>
      absurd (beq_iff_eq.mpr (h5.mpr hy)) (by simpa using h)
    refine WP.mono (recoverInvalid_ok s1) fun t ⟨kt, _, dt⟩ => ⟨k1.trans (DecKeep.of_dkeep kt), none, ?_, dt⟩
    rw [iteF hy]

end

end VG.Proof.Ed25519.RISCV64
