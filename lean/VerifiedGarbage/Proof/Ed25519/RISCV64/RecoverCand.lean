module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Recover
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
public import VerifiedGarbage.Proof.Ed25519.Recover
public import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.Field32Contract
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
import VerifiedGarbage.Proof.Ed25519.RISCV64.Freeze
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed25519.RISCV64.MulFn
public import VerifiedGarbage.Proof.Ed25519.Point32Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.Ed25519.RISCV64.FieldMemory
public import VerifiedGarbage.Spec.Ed25519
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldProg
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Freeze
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Field
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Power
public import VerifiedGarbage.Proof.X25519.Chain250
import VerifiedGarbage.Proof.X25519.RISCV64.R64.Reduce

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
