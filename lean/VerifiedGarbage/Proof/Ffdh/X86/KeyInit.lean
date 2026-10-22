module

public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Powers
import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
meta import VerifiedGarbage.Proof.Mont.X86.Words
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Powers
meta import VerifiedGarbage.Proof.Ffdh.X86.Stages
meta import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Dsa.X86.ABIResources
meta import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
meta import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa

/-! # `vg_ffdh_key_generation_init` on i686 -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.KeyInit
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.KeyInit
open VG.Impl.Mont.X86 (at_)
open VG.Proof.Bignum.X86.CrtRt (wp_cmpC)

/-- The flag `validate` computes from the borrows `c₁` (`p_len < 64`) and `c₂` (`p_len < 1025`). -/
theorem flag_zero (c₁ c₂ : Bool) :
    (((0#32 - (BitVec.ofBool c₁).setWidth 32) ^^^ 0xFFFFFFFF) &&&
        (0#32 - (BitVec.ofBool c₂).setWidth 32) &&& 1 &&&
      (((0#32 - (BitVec.ofBool c₁).setWidth 32) ^^^ 0xFFFFFFFF) &&&
        (0#32 - (BitVec.ofBool c₂).setWidth 32) &&& 1) == 0) = !(!c₁ && c₂) := by
  cases c₁ <;> cases c₂ <;> decide

/-- `ecx` the state's pointer, ZF clear exactly when `64 ≤ p_len ≤ 1024`. -/
theorem validate_ok {s : State} {S L : BitVec 32}
    (r0 : readSrc s (.mem (PublicFn.argument 0)) = some S)
    (r1 : readSrc s (.mem (PublicFn.argument 1)) = some L) :
    WP isa (.block (validate ++ ([.alu .test .edx (.reg .edx)] : List Instr))) s fun t =>
      t.gpr .ecx = S ∧ t.zf = some (!(decide (64 ≤ L.toNat) && decide (L.toNat ≤ 1024))) ∧
        t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  refine wp_movS r0 fun u1 a1 _ => ?_
  refine wp_movS (by rw [argument_keep a1.keeps (by decide) a1.mem 1]; exact r1) fun u2 a2 _ => ?_
  refine wp_movS rfl fun u0 a0 _ => ?_
  refine wp_cmpC rfl fun u3 f3 c3 => ?_
  refine wp_sbbS rfl c3 fun u4 a4 _ => ?_
  refine wp_logicS (.inr rfl) rfl fun u5 a5 => ?_
  refine wp_cmpC rfl fun u6 f6 c6 => ?_
  refine wp_sbbS rfl c6 fun u7 a7 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u8 a8 => ?_
  refine wp_logicS (.inl rfl) rfl fun u9 a9 => ?_
  refine wp_testS rfl fun t f z => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [f.gpr, a9.other _ (by decide), a8.other _ (by decide), a7.other _ (by decide), f6.gpr,
      a5.other _ (by decide), a4.other _ (by decide), f3.gpr, a0.other _ (by decide), a2.other _ (by decide),
      a1.gpr]
  · have e2 : u0.gpr .eax = L := by rw [a0.other _ (by decide), a2.gpr]
    have e5 : u5.gpr .eax = L := by
      rw [a5.other _ (by decide), a4.other _ (by decide), f3.gpr, e2]
    rw [z, a9.gpr, a8.gpr, a7.gpr, a7.other .edx (by decide), f6.gpr, a5.gpr, a4.gpr, BitVec.sub_self,
      BitVec.sub_self]
    simp only [ite_true, reduceCtorEq, ite_false, e5, e2]
    rw [flag_zero]
    have e1 : decide (64 ≤ L.toNat) = !decide (L.toNat < 64) := by
      rw [← decide_not]; exact decide_eq_decide.mpr (by omega)
    have e2 : decide (L.toNat ≤ 1024) = decide (L.toNat < 1025) := decide_eq_decide.mpr (by omega)
    rw [e1, e2]
    rfl
  · rw [f.mem, a9.mem, a8.mem, a7.mem, f6.mem, a5.mem, a4.mem, f3.mem, a0.mem, a2.mem, a1.mem]
  · have k : Keeps [.eax, .ecx, .edx] s u1 := a1.keeps.mono (by decide)
    exact (((((((((k.widen a2.keeps).widen a0.keeps).widen (f3.keeps [])).widen a4.keeps).widen a5.keeps).widen
      (f6.keeps [])).widen a7.keeps).widen a8.keeps).widen a9.keeps).widen (f.keeps [])

/-! ## The four words -/

/-- A 64-bit word, from its two 32-bit halves. -/
theorem readW64_split (m : Mem) (a : Addr) :
    m.readW a 64 = m.readW (a + BitVec.ofNat 64 4) 32 ++ m.readW a 32 := by
  rw [← VG.Proof.Rc2.Word32.readW64_hi, ← VG.Proof.Rc2.Word32.readW64_lo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split
  · simp [*]
  · simp [show i - 32 < 32 by omega]; congr 1; omega

/-- A 32-bit word through a 32-bit store at another word offset of `B`. -/
theorem read_write_ne (m : Mem) (B : Addr) {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) (v : BitVec 32) :
    (m.writeW (B + BitVec.ofNat 64 (4 * j)) v).readW (B + BitVec.ofNat 64 (4 * i)) 32 =
      m.readW (B + BitVec.ofNat 64 (4 * i)) 32 :=
  Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide)

theorem read_write_eq (m : Mem) (B : Addr) (j : Nat) (v : BitVec 32) :
    (m.writeW (B + BitVec.ofNat 64 (4 * j)) v).readW (B + BitVec.ofNat 64 (4 * j)) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

/-- The memory after the four words' stores, low halves first. -/
def stored (m : Mem) (B : Addr) (k sv w r : BitVec 32) : Mem :=
  (((((((m.writeW (B + BitVec.ofNat 64 (4 * 0)) k).writeW (B + BitVec.ofNat 64 (4 * 2)) sv).writeW
    (B + BitVec.ofNat 64 (4 * 4)) w).writeW (B + BitVec.ofNat 64 (4 * 6)) r).writeW
    (B + BitVec.ofNat 64 (4 * 1)) 0#32).writeW (B + BitVec.ofNat 64 (4 * 3)) 0#32).writeW
    (B + BitVec.ofNat 64 (4 * 5)) 0#32).writeW (B + BitVec.ofNat 64 (4 * 7)) 0#32

theorem stored_words (m : Mem) (B : Addr) (k sv w r : BitVec 32) :
    Spec.Rsa.wordsAt (stored m B k sv w r) B 4 = [0#32 ++ k, 0#32 ++ sv, 0#32 ++ w, 0#32 ++ r] := by
  have W (M : Mem) (i j k : Nat) (hj : 2 * i + 1 = j) (hk : 2 * i = k) :
      M.readW (B + BitVec.ofNat 64 (8 * i)) 64 =
        M.readW (B + BitVec.ofNat 64 (4 * j)) 32 ++ M.readW (B + BitVec.ofNat 64 (4 * k)) 32 := by
    rw [readW64_split, Offset.add_add, ← hj, ← hk]
    congr 4 <;> omega
  change [(stored m B k sv w r).readW (B + BitVec.ofNat 64 (8 * 0)) 64,
    (stored m B k sv w r).readW (B + BitVec.ofNat 64 (8 * 1)) 64,
    (stored m B k sv w r).readW (B + BitVec.ofNat 64 (8 * 2)) 64,
    (stored m B k sv w r).readW (B + BitVec.ofNat 64 (8 * 3)) 64] = _
  rw [W _ 0 1 0 rfl rfl, W _ 1 3 2 rfl rfl, W _ 2 5 4 rfl rfl, W _ 3 7 6 rfl rfl]
  simp (disch := decide) only [stored, read_write_eq, read_write_ne]

section
variable {is : List Instr} {Q : State → Prop} {S : BitVec 32}

/-- `[ecx + 4j]`, `ecx` the state. -/
theorem ea_word {u : State} (hc : u.gpr .ecx = S) (fit : S.toNat + 32 ≤ 2 ^ 32) {j : Nat} (hj : j < 8) :
    u.ea (at_ .ecx (4 * j)) = S.setWidth 64 + BitVec.ofNat 64 (4 * j) := by
  change addr (u.gpr .ecx) (4 * j) = _
  rw [hc, addr_eq (by omega)]

/-- `store [ecx + 4j], eax`. -/
theorem store_ok {u : State} (hc : u.gpr .ecx = S) (fit : S.toNat + 32 ≤ 2 ^ 32) {j : Nat} (hj : j < 8)
    (hw : InRegions u.wr (S.setWidth 64 + BitVec.ofNat 64 (4 * j)) 4)
    (k : ∀ t, Keeps [] u t → t.mem = u.mem.writeW (S.setWidth 64 + BitVec.ofNat 64 (4 * j)) (u.gpr .eax) →
      WP isa (.block is) t Q) :
    WP isa (.block (.store (at_ .ecx (4 * j)) .eax :: is)) u Q :=
  wp_storeS (ea_word hc fit hj) hw fun t m => k t (m.keeps []) m.mem

/-- `mov eax, x; store [ecx + 4j], eax`. -/
theorem pair_ok {u : State} {x : Src} {X : BitVec 32} (hx : readSrc u x = some X) (hc : u.gpr .ecx = S)
    (fit : S.toNat + 32 ≤ 2 ^ 32) {j : Nat} (hj : j < 8)
    (hw : InRegions u.wr (S.setWidth 64 + BitVec.ofNat 64 (4 * j)) 4)
    (k : ∀ t, Keeps [.eax] u t → t.gpr .eax = X →
      t.mem = u.mem.writeW (S.setWidth 64 + BitVec.ofNat 64 (4 * j)) X → WP isa (.block is) t Q) :
    WP isa (.block (.mov .eax x :: .store (at_ .ecx (4 * j)) .eax :: is)) u Q := by
  refine wp_movS hx fun v a _ => ?_
  refine store_ok (by rw [a.other _ (by decide), hc]) fit hj (by rw [a.wr]; exact hw) fun t K M => ?_
  refine k t (a.keeps.widen K) (by rw [K.1 _ (by simp), a.gpr]) ?_
  rw [M, a.gpr, a.mem]

end

/-- The four words' stores, then `eax := V`. -/
theorem words_ok {s : State} {S : BitVec 32} {ks ss ws rs : Src} {K Sv W R V : BitVec 32}
    (hc : s.gpr .ecx = S) (fit : S.toNat + 32 ≤ 2 ^ 32)
    (hw : ∀ j < 8, InRegions s.wr (S.setWidth 64 + BitVec.ofNat 64 (4 * j)) 4)
    (hk : ∀ t : State, t.gpr .edx = s.gpr .edx → readSrc t ks = some K)
    (hs : ∀ t : State, t.gpr .edx = s.gpr .edx → readSrc t ss = some Sv)
    (hw' : ∀ t : State, t.gpr .edx = s.gpr .edx → readSrc t ws = some W)
    (hr : ∀ t : State, t.gpr .edx = s.gpr .edx → readSrc t rs = some R) :
    WP isa (.block (words ks ss ws rs ++ ([.mov .eax (.imm V)] : List Instr))) s fun t =>
      t.gpr .eax = V ∧ t.mem = stored s.mem (S.setWidth 64) K Sv W R ∧ Keeps [.eax] s t := by
  have E {u : State} (k : Keeps [.eax] s u) : u.gpr .edx = s.gpr .edx := k.1 _ (by decide)
  have C {u : State} (k : Keeps [.eax] s u) : u.gpr .ecx = S := (k.1 _ (by decide)).trans hc
  have Wr {u : State} (k : Keeps [.eax] s u) {j : Nat} (hj : j < 8) :
      InRegions u.wr (S.setWidth 64 + BitVec.ofNat 64 (4 * j)) 4 := by rw [k.2.2]; exact hw j hj
  have k0 := Keeps.refl [.eax] s
  refine pair_ok (j := 0) (hk s rfl) hc fit (by decide) (hw 0 (by decide)) fun u1 j1 _ m1 => ?_
  have k1 := k0.widen j1
  refine pair_ok (j := 2) (hs u1 (E k1)) (C k1) fit (by decide) (Wr k1 (by decide)) fun u2 j2 _ m2 => ?_
  have k2 := k1.widen j2
  refine pair_ok (j := 4) (hw' u2 (E k2)) (C k2) fit (by decide) (Wr k2 (by decide)) fun u3 j3 _ m3 => ?_
  have k3 := k2.widen j3
  refine pair_ok (j := 6) (hr u3 (E k3)) (C k3) fit (by decide) (Wr k3 (by decide)) fun u4 j4 _ m4 => ?_
  have k4 := k3.widen j4
  refine wp_movS rfl fun u5 a5 _ => ?_
  have k5 := k4.widen a5.keeps
  refine store_ok (j := 1) (C k5) fit (by decide) (Wr k5 (by decide)) fun u6 j6 m6 => ?_
  have k6 := k5.widen j6
  refine store_ok (j := 3) (C k6) fit (by decide) (Wr k6 (by decide)) fun u7 j7 m7 => ?_
  have k7 := k6.widen j7
  refine store_ok (j := 5) (C k7) fit (by decide) (Wr k7 (by decide)) fun u8 j8 m8 => ?_
  have k8 := k7.widen j8
  refine store_ok (j := 7) (C k8) fit (by decide) (Wr k8 (by decide)) fun u9 j9 m9 => ?_
  have k9 := k8.widen j9
  refine wp_movS rfl fun t a _ => WP.block_nil ⟨a.gpr, ?_, k9.widen a.keeps⟩
  have z5 : u5.gpr .eax = 0#32 := a5.gpr
  have z6 : u6.gpr .eax = 0#32 := (j6.1 _ List.not_mem_nil).trans z5
  have z7 : u7.gpr .eax = 0#32 := (j7.1 _ List.not_mem_nil).trans z6
  have z8 : u8.gpr .eax = 0#32 := (j8.1 _ List.not_mem_nil).trans z7
  rw [a.mem, m9, m8, m7, m6, a5.mem, m4, m3, m2, m1, z8, z7, z6, z5]
  rfl

theorem stored_frame (m : Mem) (B : Addr) (k sv w r : BitVec 32) :
    Frame [⟨B, 128⟩] m (stored m B k sv w r) := by
  have c (j : Nat) (hj : j < 8) : (⟨B, 128⟩ : Region).Contains (B + BitVec.ofNat 64 (4 * j)) (32 / 8) :=
    Offset.contains_base B (by omega) (by omega)
  have h := Frame.refl [⟨B, 128⟩] m
  exact ((((((((h.writeW (List.mem_singleton_self _) k (c 0 (by decide))).writeW (List.mem_singleton_self _)
    sv (c 2 (by decide))).writeW (List.mem_singleton_self _) w (c 4 (by decide))).writeW
    (List.mem_singleton_self _) r (c 6 (by decide))).writeW (List.mem_singleton_self _) 0#32
    (c 1 (by decide))).writeW (List.mem_singleton_self _) 0#32 (c 3 (by decide))).writeW
    (List.mem_singleton_self _) 0#32 (c 5 (by decide))).writeW (List.mem_singleton_self _) 0#32 (c 7 (by decide)))

/-- What `vg_ffdh_key_generation_init` is given. -/
structure ABI (s : State) : Prop where
  stackBound : (s.gpr .esp).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 8⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 128⟩]
  outArgs : (⟨(arg s 0).setWidth 64, 128⟩ : Region).Disjoint ⟨argAddr s 0, 8⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 128⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 8⟩
  outBound : (arg s 0).toNat + 128 ≤ 2 ^ 32

theorem abi_of {s : State} (h : (Spec.Ffdh.keyInitContract abi).pre s) : ABI s := by
  sig_pre [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem ABI.read {s : State} (A : ABI s) {i : Nat} (hi : i < 2) :
    readSrc s (.mem (PublicFn.argument i)) = some (arg s i) :=
  (VG.Proof.Dsa.X86.stackArgument_of (count := 2) (by have := A.stackBound; omega) hi
    (by rw [A.rd]; exact List.mem_append_left _ (List.mem_singleton_self _)) A.outArgs.symm).readSrc

/-- The words stored, as numbers. -/
def values (valid : Bool) (len : BitVec 32) : List (BitVec 32) :=
  if valid then [128, 128, len, len] else [0, 0, 0, 0]

theorem code_ok {s : State} (A : ABI s) :
    WP isa code s fun t =>
      t.gpr .eax = (if 64 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 1024 then 1 else 0) ∧
      t.mem = (if 64 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 1024 then
          stored s.mem ((arg s 0).setWidth 64) 128 128 (arg s 1) (arg s 1)
        else stored s.mem ((arg s 0).setWidth 64) 0 0 0 0) ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have hw {u : State} (hu : u.wr = s.wr) (j : Nat) (hj : j < 8) :
      InRegions u.wr ((arg s 0).setWidth 64 + BitVec.ofNat 64 (4 * j)) 4 :=
    ⟨_, by rw [hu, A.wr]; exact List.mem_singleton_self _,
      Offset.contains_base _ (by omega) (by omega)⟩
  have fit : (arg s 0).toNat + 32 ≤ 2 ^ 32 := by have := A.outBound; omega
  unfold code
  refine WP.seq (WP.mono (validate_ok (A.read (by decide)) (A.read (by decide))) fun u ⟨hc, hz, hm, k⟩ => ?_)
  refine WP.ite _ hz (fun hb => ?_) fun hb => ?_
  · have hn : ¬(64 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 1024) := by
      intro h; simp [h.1, h.2] at hb
    refine WP.mono (words_ok hc fit (hw k.2.2) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl)) fun t ⟨ha, tm, k'⟩ => ⟨by rw [ha, ite_eq_right hn], by rw [tm, hm, ite_eq_right hn], k.widen k'⟩
  · have hv : 64 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 1024 := by
      simpa only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] using hb
    have r1 : readSrc u (.mem (PublicFn.argument 1)) = some (arg s 1) := by
      rw [argument_keep k (by decide) hm 1]; exact A.read (by decide)
    refine wp_movS r1 fun v a _ => ?_
    have kv : Keeps [.eax, .ecx, .edx] s v := k.widen a.keeps
    refine WP.mono (words_ok (W := arg s 1) (R := arg s 1) (by rw [a.other _ (by decide), hc]) fit (hw kv.2.2) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun t ht => by rw [show readSrc t (.reg .edx) = some (t.gpr .edx) from rfl, ht, a.gpr])
      (fun t ht => by rw [show readSrc t (.reg .edx) = some (t.gpr .edx) from rfl, ht, a.gpr]))
      fun t ⟨ha, tm, k'⟩ => ⟨by rw [ha, ite_eq_left hv], by rw [tm, a.mem, hm, ite_eq_left hv], kv.widen k'⟩

theorem correct (s : State) (h : (Spec.Ffdh.keyInitContract abi).pre s) :
    ∃ trace t, Exec isa code s trace t ∧ abiPreserved s t ∧ (Spec.Ffdh.keyInitContract abi).post s t := by
  have A := abi_of h
  obtain ⟨tr, t, E, ha, hm, k⟩ := code_ok A
  have F : ∀ (K Sv W R : BitVec 32), Frame [⟨(arg s 0).setWidth 64, 128⟩] s.mem
      (stored s.mem ((arg s 0).setWidth 64) K Sv W R) := fun _ _ _ _ => stored_frame _ _ _ _ _ _
  refine ⟨tr, t, E, ⟨fun r hr => k.1 r (by revert r; decide), ?_⟩, ?_⟩
  · have F' : Frame [⟨(arg s 0).setWidth 64, 128⟩] s.mem t.mem := by
      rw [hm]; split <;> exact F _ _ _ _
    exact F'.readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact A.retOut) (by decide)
  · sig_post [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right, ha, hm]
    by_cases hv : 64 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 1024
    · have e : Spec.Ffdh.keyInit (arg s 1).toNat = some [128, 128, (arg s 1).toNat, (arg s 1).toNat] := by
        simp [Spec.Ffdh.keyInit, hv.1, hv.2]
      rw [e, ite_eq_left hv, ite_eq_left hv, stored_words]
      have w : 0#32 ++ arg s 1 = BitVec.ofNat 64 (arg s 1).toNat := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_append, BitVec.toNat_ofNat]
        simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
        exact (Nat.mod_eq_of_lt (by have := (arg s 1).isLt; omega)).symm
      refine ⟨rfl, ?_⟩
      rw [w]
      rfl
    · have e : Spec.Ffdh.keyInit (arg s 1).toNat = none := by
        simp only [Spec.Ffdh.keyInit]
        rw [ite_eq_right]
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hv
      rw [e, ite_eq_right hv, ite_eq_right hv, stored_words]
      exact ⟨rfl, rfl⟩

theorem args_out {s : State} (A : ABI s) : ArgsOut 2 s := by
  refine ⟨A.stackBound, fun r hr => ?_⟩
  rw [A.wr] at hr
  obtain rfl := List.mem_singleton.mp hr
  intro a ha hb
  let j := (a - (s.gpr .esp).setWidth 64).toNat
  have hj : j < 12 := by change j + 1 ≤ 12 at ha; omega
  have he : (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 j = a := by
    change (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (a - (s.gpr .esp).setWidth 64).toNat = a
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have a0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by have := A.stackBound; omega)
  by_cases h : j < 4
  · exact A.retOut a (by rw [← he]; exact Offset.contains_base _ (by omega) (by omega)) hb
  · exact A.outArgs a hb (by rw [a0, ← he]; exact Offset.contains _ (by omega) (by omega) (by decide))

theorem constantTime : ConstantTime isa (Spec.Ffdh.keyInitContract abi).pre
    (Spec.Ffdh.keyInitContract abi).pub code := by
  refine VG.Taint.constantTime (A := VG.X86.taint) (argTaint [] 12) ?_ (by taint_decide)
  intro s t hs ht H
  sig_pub [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, a0, a1⟩ := H
  refine agree_argTaint (k := 2) (fun _ h => nomatch h) SP (args_out (abi_of hs)) (args_out (abi_of ht)) ?_
  intro i hi
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · exact a0
  · exact a1

/-- The state at `0x1000`, `p_len` 64, the arguments at `0x4004`. -/
def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4008 then 64 else 0
  rd := [⟨0x4004, 8⟩]
  wr := [⟨0x1000, 128⟩]

theorem satisfiable : ∃ s, (Spec.Ffdh.keyInitContract abi).pre s := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  have esp : satState.gpr .esp = 0x4000 := rfl
  sig_implies_sat [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig, abi, argSlots, argVal, argBytes,
    stackBelow] [a0, e, esp, satState] using satState

theorem verified : Verified target code (Spec.Ffdh.keyInitContract abi) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.KeyInit
