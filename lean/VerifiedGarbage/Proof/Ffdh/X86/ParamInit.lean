module

public import VerifiedGarbage.Impl.Ffdh.X86.ParamInit
import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
meta import VerifiedGarbage.Proof.Dsa.X86.ABIResources
meta import VerifiedGarbage.Impl.Ffdh.X86.ParamInit
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
meta import VerifiedGarbage.Spec.Ffdh.GenerationContract
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Ffdh.KeyGeneration
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # `vg_ffdh_parameter_generation_init` on i686 -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.ParamInit
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.ParamInit
open VG.Impl.Mont.X86 (at_)
open VG.Proof.Ffdh.X86.KeyInit (readW64_split read_write_eq read_write_ne ea_word)

/-- The memory after 32-bit stores at the word offsets `4 j` of `B`, in order. -/
def writes (m : Mem) (B : Addr) : List (Nat × BitVec 32) → Mem
  | [] => m
  | (j, v) :: l => writes (m.writeW (B + BitVec.ofNat 64 (4 * j)) v) B l

theorem writes_frame (m : Mem) (B : Addr) :
    ∀ l : List (Nat × BitVec 32), (∀ p ∈ l, p.1 < 8) → Frame [⟨B, 128⟩] m (writes m B l)
  | [] , _ => Frame.refl _ _
  | (j, v) :: l, h => by
    have hj : j < 8 := h (j, v) (List.mem_cons_self ..)
    exact ((Frame.refl [⟨B, 128⟩] m).writeW (List.mem_singleton_self _) v
      (Offset.contains_base B (by omega) (by omega))).trans
      (writes_frame _ B l fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- What the function is given. -/
structure ABI (s : State) : Prop where
  stackBound : (s.gpr .esp).toNat + 4 + 12 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 12⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 128⟩]
  outArgs : (⟨(arg s 0).setWidth 64, 128⟩ : Region).Disjoint ⟨argAddr s 0, 12⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 128⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 12⟩
  outBound : (arg s 0).toNat + 128 ≤ 2 ^ 32

theorem abi_of {s : State} (h : (Spec.Ffdh.parameterInitContract abi).pre s) : ABI s := by
  sig_pre [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem ABI.read {s : State} (A : ABI s) {i : Nat} (hi : i < 3) :
    readSrc s (.mem (PublicFn.argument i)) = some (arg s i) :=
  (VG.Proof.Dsa.X86.stackArgument_of (count := 3) (by have := A.stackBound; omega) hi
    (by rw [A.rd]; exact List.mem_append_left _ (List.mem_singleton_self _)) A.outArgs.symm).readSrc

/-- The arguments read the same after stores into the state. -/
theorem ABI.read_after {s u : State} (A : ABI s) {i : Nat} (hi : i < 3) (sp : u.gpr .esp = s.gpr .esp)
    (rd : u.rd = s.rd) (wr : u.wr = s.wr) (F : Frame [⟨(arg s 0).setWidth 64, 128⟩] s.mem u.mem) :
    readSrc u (.mem (PublicFn.argument i)) = some (arg s i) := by
  have R := A.read hi
  have e : u.ea (PublicFn.argument i) = s.ea (PublicFn.argument i) := by
    simp only [State.ea, PublicFn.argument, at_, sp]
  have hin : InRegions (s.rd ++ s.wr) (s.ea (PublicFn.argument i)) 4 := by
    change s.load32 (s.ea _) = _ at R
    simp only [State.load32] at R
    split at R
    · assumption
    · cases R
  have c : (⟨argAddr s 0, 12⟩ : Region).Contains (s.ea (PublicFn.argument i)) (32 / 8) := by
    have a0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
      addr_eq (by have := A.stackBound; omega)
    have ea : s.ea (PublicFn.argument i) = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
      change addr (s.gpr .esp) (4 + 4 * i) = _
      exact addr_eq (by have := A.stackBound; omega)
    rw [ea, a0]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  change u.load32 (u.ea _) = _
  change s.load32 (s.ea _) = _ at R
  rw [e]
  simp only [State.load32, rd, wr, hin, ↓reduceIte] at R ⊢
  rw [F.readW c (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact A.outArgs.symm) (by decide)]
  exact R

section
variable {is : List Instr} {Q : State → Prop} {S : BitVec 32}

/-- `store [ecx + d], r` for `d = 4 j`. -/
theorem store_ok {u : State} {r : Reg} (hc : u.gpr .ecx = S) (fit : S.toNat + 32 ≤ 2 ^ 32) {j : Nat}
    (hj : j < 8) (hw : InRegions u.wr (S.setWidth 64 + BitVec.ofNat 64 (4 * j)) 4)
    (k : ∀ t, Keeps [] u t → t.rd = u.rd → t.wr = u.wr →
      t.mem = u.mem.writeW (S.setWidth 64 + BitVec.ofNat 64 (4 * j)) (u.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (.store (at_ .ecx (4 * j)) r :: is)) u Q :=
  wp_storeS (ea_word hc fit hj) hw fun t m => k t (m.keeps []) m.rd m.wr m.mem

end

/-- The parameters' validity. -/
abbrev Valid (bits gen : Nat) : Prop := 512 ≤ bits ∧ bits ≤ 8192 ∧ (gen = 2 ∨ gen = 5)

/-- The stores of `clear`. -/
def cleared : List (Nat × BitVec 32) := (List.range 8).map fun j => (j, 0#32)

/-- The stores of `initialize`, from `bits`. -/
def initial (bits : Nat) : List (Nat × BitVec 32) :=
  [(0, BitVec.ofNat 32 (bits * bits * 64)), (1, BitVec.ofNat 32 (bits * bits * 64 / 2 ^ 32)),
    (2, BitVec.ofNat 32 ((bits + 7) / 8)), (4, BitVec.ofNat 32 (32769 * ((bits + 7) / 8))),
    (6, BitVec.ofNat 32 (512 * ((bits + 7) / 8))), (3, 0#32), (5, 0#32), (7, 0#32)]

/-- What remains of the code from a state that read the stores so far. -/
structure Cur (s u : State) (l : List (Nat × BitVec 32)) : Prop where
  esp : u.gpr .esp = s.gpr .esp
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mem : u.mem = writes s.mem ((arg s 0).setWidth 64) l
  keeps : Keeps [.eax, .ecx, .edx] s u

theorem writes_append (m : Mem) (B : Addr) (l l' : List (Nat × BitVec 32)) :
    writes m B (l ++ l') = writes (writes m B l) B l' := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih => obtain ⟨j, v⟩ := p; exact ih _

theorem Cur.frame {s u : State} {l : List (Nat × BitVec 32)} (C : Cur s u l) (hl : ∀ p ∈ l, p.1 < 8) :
    Frame [⟨(arg s 0).setWidth 64, 128⟩] s.mem u.mem := by
  rw [C.mem]; exact writes_frame _ _ l hl

/-- A store at word `j` with `ecx` the state. -/
theorem Cur.store {is : List Instr} {Q : State → Prop} {s u : State} {l : List (Nat × BitVec 32)} (A : ABI s) (C : Cur s u l)
    (hc : u.gpr .ecx = arg s 0) {r : Reg} {j : Nat} (hj : j < 8)
    (k : ∀ t, Cur s t (l ++ [(j, u.gpr r)]) → (∀ q, t.gpr q = u.gpr q) → WP isa (.block is) t Q) :
    WP isa (.block (.store (at_ .ecx (4 * j)) r :: is)) u Q := by
  refine store_ok hc (by have := A.outBound; omega) hj ?_ fun t K rd wr m => k t ⟨?_, ?_, ?_, ?_, ?_⟩ ?_
  · exact ⟨_, by rw [C.wr, A.wr]; exact List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [K.1 _ (by simp), C.esp]
  · rw [rd, C.rd]
  · rw [wr, C.wr]
  · rw [m, C.mem, writes_append]; rfl
  · exact C.keeps.widen K
  · exact fun q => K.1 q (by simp)

theorem Cur.step {s u t : State} {l : List (Nat × BitVec 32)} (C : Cur s u l) {rs : List Reg}
    (K : Keeps rs u t) (hrs : ∀ r ∈ rs, r = .eax ∨ r = .ecx ∨ r = .edx) (hm : t.mem = u.mem) : Cur s t l := by
  have sp : .esp ∉ rs := fun h => by rcases hrs _ h with h | h | h <;> cases h
  refine ⟨(K.1 _ sp).trans C.esp, K.2.1.trans C.rd, K.2.2.trans C.wr, hm.trans C.mem, ?_⟩
  exact C.keeps.widen K fun r hr => by rcases hrs r hr with rfl | rfl | rfl <;> simp

theorem clear_ok {s u : State} (A : ABI s) (C : Cur s u []) :
    WP isa (.block clear) u fun t => t.gpr .eax = 0 ∧ Cur s t cleared := by
  unfold clear
  refine wp_movS (A.read_after (by decide) C.esp C.rd C.wr (C.frame (by simp))) fun u1 a1 _ => ?_
  have C1 := C.step a1.keeps (by simp) a1.mem
  refine wp_movS rfl fun u2 a2 _ => ?_
  have C2 := C1.step a2.keeps (by simp) a2.mem
  have hc : u2.gpr .ecx = arg s 0 := by rw [a2.other _ (by decide), a1.gpr]
  have z : u2.gpr .eax = 0 := a2.gpr
  refine C2.store (j := 0) A hc (by decide) fun t3 C3 g3 => ?_
  refine C3.store (j := 1) A (by rw [g3, hc]) (by decide) fun t4 C4 g4 => ?_
  refine C4.store (j := 2) A (by rw [g4, g3, hc]) (by decide) fun t5 C5 g5 => ?_
  refine C5.store (j := 3) A (by rw [g5, g4, g3, hc]) (by decide) fun t6 C6 g6 => ?_
  refine C6.store (j := 4) A (by rw [g6, g5, g4, g3, hc]) (by decide) fun t7 C7 g7 => ?_
  refine C7.store (j := 5) A (by rw [g7, g6, g5, g4, g3, hc]) (by decide) fun t8 C8 g8 => ?_
  refine C8.store (j := 6) A (by rw [g8, g7, g6, g5, g4, g3, hc]) (by decide) fun t9 C9 g9 => ?_
  refine C9.store (j := 7) A (by rw [g9, g8, g7, g6, g5, g4, g3, hc]) (by decide) fun t C g => ?_
  refine WP.block_nil ⟨by rw [g, g9, g8, g7, g6, g5, g4, g3, z], ?_⟩
  simp only [g9, g8, g7, g6, g5, g4, g3, z, List.nil_append, List.cons_append] at C
  exact C

/-- `eax := L`, from the state's bits `B`. -/
theorem width_ok {is : List Instr} {Q : State → Prop} {s u : State} {l : List (Nat × BitVec 32)} (A : ABI s)
    (C : Cur s u l) (hl : ∀ p ∈ l, p.1 < 8) (hb : (arg s 1).toNat ≤ 8192)
    (k : ∀ t, Cur s t l → t.gpr .eax = BitVec.ofNat 32 (((arg s 1).toNat + 7) / 8) → t.gpr .ecx = u.gpr .ecx →
      WP isa (.block is) t Q) :
    WP isa (.block (width ++ is)) u Q := by
  unfold width
  refine wp_movS (A.read_after (by decide) C.esp C.rd C.wr (C.frame hl)) fun u1 a1 _ => ?_
  refine wp_addi fun u2 a2 => ?_
  refine wp_shr (by decide) fun t a3 _ => ?_
  have C3 := ((C.step a1.keeps (by simp) a1.mem).step a2.keeps (by simp) a2.mem).step a3.keeps (by simp) a3.mem
  refine k t C3 ?_ ?_
  · rw [a3.gpr, a2.gpr, a1.gpr]
    apply BitVec.eq_of_toNat_eq
    have b := (arg s 1).isLt
    have h7 : (7 : BitVec 32).toNat = 7 := rfl
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h7]
    omega
  · rw [a3.other _ (by decide), a2.other _ (by decide), a1.other _ (by decide)]

theorem mul_val (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a).toNat * (BitVec.ofNat 32 b).toNat = a * b := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem mul_lit (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a).toNat * (OfNat.ofNat b : BitVec 32).toNat = a * b :=
  mul_val a b ha hb

theorem setup_ok {s u : State} (A : ABI s) (C : Cur s u []) (hb : (arg s 1).toNat ≤ 8192) :
    WP isa (.block setup) u fun t => t.gpr .eax = 1 ∧ Cur s t (initial (arg s 1).toNat) := by
  have bl := (arg s 1).isLt
  unfold setup
  refine wp_movS (A.read_after (by decide) C.esp C.rd C.wr (C.frame (by simp))) fun u1 a1 _ => ?_
  have C1 := C.step a1.keeps (by simp) a1.mem
  refine wp_mul fun u2 a2 => ?_
  have C2 := C1.step a2.keeps (by simp) a2.mem
  have sq : (arg s 1).toNat * (arg s 1).toNat < 2 ^ 32 := by
    have := Nat.mul_le_mul hb hb; omega
  have e2 : u2.gpr .eax = BitVec.ofNat 32 ((arg s 1).toNat * (arg s 1).toNat) := by
    rw [a2.eax, a1.gpr]
  refine wp_movS rfl fun u3 a3 _ => ?_
  have C3 := C2.step a3.keeps (by simp) a3.mem
  refine wp_mul fun u4 a4 => ?_
  have C4 := C3.step a4.keeps (by simp) a4.mem
  have p4 : (u3.gpr .eax).toNat * (u3.gpr .edx).toNat = (arg s 1).toNat * (arg s 1).toNat * 64 := by
    rw [a3.gpr, a3.other _ (by decide), e2]
    exact mul_lit _ _ sq (by decide)
  refine wp_movS (A.read_after (by decide) C4.esp C4.rd C4.wr (C4.frame (by simp))) fun u5 a5 _ => ?_
  have C5 := C4.step a5.keeps (by simp) a5.mem
  have hc : u5.gpr .ecx = arg s 0 := a5.gpr
  refine C5.store (j := 0) A hc (by decide) fun t6 C6 g6 => ?_
  refine C6.store (j := 1) (r := .edx) A (by rw [g6, hc]) (by decide) fun t7 C7 g7 => ?_
  refine width_ok A C7 (by simp) hb fun u8 C8 e8 c8 => ?_
  refine C8.store (j := 2) A (by rw [c8, g7, g6, hc]) (by decide) fun t9 C9 g9 => ?_
  refine wp_movS rfl fun u10 a10 _ => ?_
  have C10 := C9.step a10.keeps (by simp) a10.mem
  refine wp_mul fun u11 a11 => ?_
  have C11 := C10.step a11.keeps (by simp) a11.mem
  have hc11 : u11.gpr .ecx = arg s 0 := by
    rw [a11.other _ (by decide) (by decide), a10.other _ (by decide), g9, c8, g7, g6, hc]
  refine C11.store (j := 4) A hc11 (by decide) fun t12 C12 g12 => ?_
  refine width_ok A C12 (by simp) hb fun u13 C13 e13 c13 => ?_
  refine wp_movS rfl fun u14 a14 _ => ?_
  have C14 := C13.step a14.keeps (by simp) a14.mem
  refine wp_mul fun u15 a15 => ?_
  have C15 := C14.step a15.keeps (by simp) a15.mem
  have hc15 : u15.gpr .ecx = arg s 0 := by
    rw [a15.other _ (by decide) (by decide), a14.other _ (by decide), c13, g12, hc11]
  refine C15.store (j := 6) A hc15 (by decide) fun t16 C16 g16 => ?_
  refine wp_movS rfl fun u17 a17 _ => ?_
  have C17 := C16.step a17.keeps (by simp) a17.mem
  have hc17 : u17.gpr .ecx = arg s 0 := by rw [a17.other _ (by decide), g16, hc15]
  refine C17.store (j := 3) A hc17 (by decide) fun t18 C18 g18 => ?_
  refine C18.store (j := 5) A (by rw [g18, hc17]) (by decide) fun t19 C19 g19 => ?_
  refine C19.store (j := 7) A (by rw [g19, g18, hc17]) (by decide) fun t20 C20 g20 => ?_
  refine wp_movS rfl fun t a _ => WP.block_nil ⟨a.gpr, ?_⟩
  have C21 := C20.step a.keeps (by simp) a.mem
  have L : ((arg s 1).toNat + 7) / 8 < 2 ^ 32 := by omega
  have v0 : u5.gpr .eax = BitVec.ofNat 32 ((arg s 1).toNat * (arg s 1).toNat * 64) := by
    rw [a5.other _ (by decide), a4.eax, p4]
  have v1 : u5.gpr .edx = BitVec.ofNat 32 ((arg s 1).toNat * (arg s 1).toNat * 64 / 2 ^ 32) := by
    rw [a5.other _ (by decide), a4.edx, p4]
  have v4 : u11.gpr .eax = BitVec.ofNat 32 (32769 * (((arg s 1).toNat + 7) / 8)) := by
    rw [a11.eax, a10.other _ (by decide), a10.gpr, g9, e8, mul_lit _ _ L (by decide), Nat.mul_comm]
  have v6 : u15.gpr .eax = BitVec.ofNat 32 (512 * (((arg s 1).toNat + 7) / 8)) := by
    rw [a15.eax, a14.other _ (by decide), a14.gpr, e13, mul_lit _ _ L (by decide), Nat.mul_comm]
  have z : u17.gpr .eax = 0#32 := a17.gpr
  simp only [g19, g18, g6, z, v6, v4, e8, v1, v0, List.nil_append, List.cons_append] at C21
  exact C21

theorem Cur.refl (s : State) : Cur s s [] := ⟨rfl, rfl, rfl, rfl, Keeps.refl _ _⟩

theorem zf_eq (G : BitVec 32) {k : Nat} (hk : k < 2 ^ 32) :
    (G - BitVec.ofNat 32 k == 0) = decide (G.toNat = k) := by
  have e : G = BitVec.ofNat 32 G.toNat := ((BitVec.ofNat_toNat 32 G).trans (BitVec.setWidth_eq G)).symm
  rw [e, sub_beq (BitVec.isLt _) hk, ← e]

/-- What `code` leaves: the status and the stores. -/
theorem code_ok {s : State} (A : ABI s) :
    WP isa code s fun t =>
      t.gpr .eax = (if Valid (arg s 1).toNat (arg s 2).toNat then 1 else 0) ∧
      Cur s t (if Valid (arg s 1).toNat (arg s 2).toNat then initial (arg s 1).toNat else cleared) := by
  have C := Cur.refl s
  unfold code
  have h1 : WP isa (.block [.mov .edx (.mem (PublicFn.argument 1)), .alu .cmp .edx (.imm 512)]) s
      fun u => u.cf = some (decide ((arg s 1).toNat < 512)) ∧ u.gpr .edx = arg s 1 ∧ Cur s u [] := by
    refine wp_movS (A.read (by decide)) fun u1 a1 _ => ?_
    refine wp_cmpi fun u2 f2 c2 _ => WP.block_nil ⟨by rw [c2, a1.gpr]; rfl, by rw [f2.gpr, a1.gpr], ?_⟩
    exact (C.step a1.keeps (by simp) a1.mem).step (f2.keeps []) (by simp) f2.mem
  refine WP.seq (WP.mono h1 fun u ⟨cu, du, Cu⟩ => ?_)
  refine WP.ite _ cu (fun hb => ?_) fun hb => ?_
  · have nv : ¬Valid (arg s 1).toNat (arg s 2).toNat := fun h => by
      simp only [decide_eq_true_eq] at hb; omega
    exact WP.mono (clear_ok A Cu) fun t ⟨ha, Ct⟩ => ⟨by rw [ha, ite_eq_right nv], by rw [ite_eq_right nv]; exact Ct⟩
  have lo : 512 ≤ (arg s 1).toNat := by simp only [decide_eq_false_iff_not] at hb; omega
  have h2 : WP isa (.block [.alu .cmp .edx (.imm 8193)]) u
      fun u => u.cf = some (decide ((arg s 1).toNat < 8193)) ∧ Cur s u [] :=
    wp_cmpi fun u2 f2 c2 _ => WP.block_nil ⟨by rw [c2, du]; rfl, Cu.step (f2.keeps []) (by simp) f2.mem⟩
  refine WP.seq (WP.mono h2 fun u ⟨cu, Cu⟩ => ?_)
  refine WP.ite _ (show isa.eval .ae u = some (!decide ((arg s 1).toNat < 8193)) by
    change u.cf.map (!·) = _; rw [cu]; rfl) (fun hb => ?_) fun hb => ?_
  · have nv : ¬Valid (arg s 1).toNat (arg s 2).toNat := fun h => by
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hb; omega
    exact WP.mono (clear_ok A Cu) fun t ⟨ha, Ct⟩ => ⟨by rw [ha, ite_eq_right nv], by rw [ite_eq_right nv]; exact Ct⟩
  have hi : (arg s 1).toNat ≤ 8192 := by simp only [Bool.not_eq_false', decide_eq_true_eq] at hb; omega
  have h3 : WP isa (.block [.mov .eax (.mem (PublicFn.argument 2)), .alu .cmp .eax (.imm 2)]) u
      fun u => u.zf = some (decide ((arg s 2).toNat = 2)) ∧ u.gpr .eax = arg s 2 ∧ Cur s u [] := by
    refine wp_movS (A.read_after (by decide) Cu.esp Cu.rd Cu.wr (Cu.frame (by simp))) fun u1 a1 _ => ?_
    refine wp_cmpi fun u2 f2 _ z2 => WP.block_nil ⟨?_, by rw [f2.gpr, a1.gpr], ?_⟩
    · rw [z2, a1.gpr]; exact congrArg some (zf_eq (arg s 2) (k := 2) (by decide))
    · exact (Cu.step a1.keeps (by simp) a1.mem).step (f2.keeps []) (by simp) f2.mem
  refine WP.seq (WP.mono h3 fun u ⟨zu, eu, Cu⟩ => ?_)
  refine WP.ite _ zu (fun hg => ?_) fun hg => ?_
  · have v : Valid (arg s 1).toNat (arg s 2).toNat := ⟨lo, hi, .inl (by simpa using hg)⟩
    exact WP.mono (setup_ok A Cu hi) fun t ⟨ha, Ct⟩ => ⟨by rw [ha, ite_eq_left v], by rw [ite_eq_left v]; exact Ct⟩
  have n2 : (arg s 2).toNat ≠ 2 := by simpa using hg
  have h4 : WP isa (.block [.alu .cmp .eax (.imm 5)]) u
      fun u => u.zf = some (decide ((arg s 2).toNat = 5)) ∧ Cur s u [] := by
    refine wp_cmpi fun u2 f2 _ z2 => WP.block_nil ⟨?_, Cu.step (f2.keeps []) (by simp) f2.mem⟩
    rw [z2, eu]; exact congrArg some (zf_eq (arg s 2) (k := 5) (by decide))
  refine WP.seq (WP.mono h4 fun u ⟨zu, Cu⟩ => ?_)
  refine WP.ite _ zu (fun hg => ?_) fun hg => ?_
  · have v : Valid (arg s 1).toNat (arg s 2).toNat := ⟨lo, hi, .inr (by simpa using hg)⟩
    exact WP.mono (setup_ok A Cu hi) fun t ⟨ha, Ct⟩ => ⟨by rw [ha, ite_eq_left v], by rw [ite_eq_left v]; exact Ct⟩
  · have nv : ¬Valid (arg s 1).toNat (arg s 2).toNat := fun h => by
      rcases h.2.2 with h | h
      · exact n2 h
      · simp [h] at hg
    exact WP.mono (clear_ok A Cu) fun t ⟨ha, Ct⟩ => ⟨by rw [ha, ite_eq_right nv], by rw [ite_eq_right nv]; exact Ct⟩

/-! ## The words -/

theorem halves {x : Nat} (hx : x < 2 ^ 64) :
    BitVec.ofNat 32 (x / 2 ^ 32) ++ BitVec.ofNat 32 x = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.ofNat 32 x).isLt, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x / 2 ^ 32 < 2 ^ 32 by omega), Nat.mod_eq_of_lt hx]
  omega

theorem zero_half {x : Nat} (hx : x < 2 ^ 32) : 0#32 ++ BitVec.ofNat 32 x = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, show (0#32 : BitVec 32).toNat = 0 from rfl,
    Nat.zero_shiftLeft, Nat.zero_or]
  omega

/-- The four 64-bit words from their eight 32-bit halves. -/
theorem words_halves (M : Mem) (B : Addr) :
    Spec.Rsa.wordsAt M B 4 =
      [M.readW (B + BitVec.ofNat 64 (4 * 1)) 32 ++ M.readW (B + BitVec.ofNat 64 (4 * 0)) 32,
        M.readW (B + BitVec.ofNat 64 (4 * 3)) 32 ++ M.readW (B + BitVec.ofNat 64 (4 * 2)) 32,
        M.readW (B + BitVec.ofNat 64 (4 * 5)) 32 ++ M.readW (B + BitVec.ofNat 64 (4 * 4)) 32,
        M.readW (B + BitVec.ofNat 64 (4 * 7)) 32 ++ M.readW (B + BitVec.ofNat 64 (4 * 6)) 32] := by
  have W (i j k : Nat) (hj : 2 * i + 1 = j) (hk : 2 * i = k) :
      M.readW (B + BitVec.ofNat 64 (8 * i)) 64 =
        M.readW (B + BitVec.ofNat 64 (4 * j)) 32 ++ M.readW (B + BitVec.ofNat 64 (4 * k)) 32 := by
    rw [readW64_split, Offset.add_add, ← hj, ← hk]
    congr 4 <;> omega
  change [M.readW (B + BitVec.ofNat 64 (8 * 0)) 64, M.readW (B + BitVec.ofNat 64 (8 * 1)) 64,
    M.readW (B + BitVec.ofNat 64 (8 * 2)) 64, M.readW (B + BitVec.ofNat 64 (8 * 3)) 64] = _
  rw [W 0 1 0 rfl rfl, W 1 3 2 rfl rfl, W 2 5 4 rfl rfl, W 3 7 6 rfl rfl]

theorem cleared_words (m : Mem) (B : Addr) : Spec.Rsa.wordsAt (writes m B cleared) B 4 = List.replicate 4 0 := by
  rw [words_halves]
  simp (disch := decide) only [cleared, List.range, List.range.loop, List.map, writes, read_write_eq,
    read_write_ne]
  rfl

theorem initial_words (m : Mem) (B : Addr) {b : Nat} (hb : b ≤ 8192) :
    Spec.Rsa.wordsAt (writes m B (initial b)) B 4 =
      [b * b * 64, (b + 7) / 8, 32769 * ((b + 7) / 8), 512 * ((b + 7) / 8)].map (BitVec.ofNat 64) := by
  rw [words_halves]
  simp (disch := decide) only [initial, writes, read_write_eq, read_write_ne]
  have sq : b * b * 64 < 2 ^ 64 := by have := Nat.mul_le_mul hb hb; omega
  rw [halves sq, zero_half (by omega), zero_half (by omega), zero_half (by omega)]
  rfl

theorem final_frame {s t : State} {v : Prop} [Decidable v]
    (C : Cur s t (if v then initial (arg s 1).toNat else cleared)) :
    Frame [⟨(arg s 0).setWidth 64, 128⟩] s.mem t.mem := by
  refine C.frame ?_
  split
  · intro p hp; simp only [initial, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
  · intro p hp; simp only [cleared, List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp; exact hj

theorem correct (s : State) (h : (Spec.Ffdh.parameterInitContract abi).pre s) :
    ∃ trace t, Exec isa code s trace t ∧ abiPreserved s t ∧ (Spec.Ffdh.parameterInitContract abi).post s t := by
  have A := abi_of h
  obtain ⟨tr, t, E, ha, C⟩ := code_ok A
  refine ⟨tr, t, E, ⟨fun r hr => C.keeps.1 r (by revert r; decide), ?_⟩, ?_⟩
  · exact (final_frame C).readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact A.retOut) (by decide)
  · sig_post [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right, ha, C.mem]
    by_cases hv : Valid (arg s 1).toNat (arg s 2).toNat
    · have e : Spec.Ffdh.parameterInit (arg s 1).toNat (arg s 2).toNat =
          some [(arg s 1).toNat * (arg s 1).toNat * 64, ((arg s 1).toNat + 7) / 8,
            32769 * (((arg s 1).toNat + 7) / 8), 512 * (((arg s 1).toNat + 7) / 8)] := by
        obtain ⟨h1, h2, h3⟩ := hv
        simp only [Spec.Ffdh.parameterInit, Spec.Ffdh.parameterAttempts, Spec.Ffdh.parameterEntropy, h1, h2,
          decide_true, Bool.true_and]
        rcases h3 with h3 | h3 <;> simp [h3]
      rw [e, ite_eq_left hv, ite_eq_left hv, initial_words _ _ hv.2.1]
      exact ⟨rfl, rfl⟩
    · have e : Spec.Ffdh.parameterInit (arg s 1).toNat (arg s 2).toNat = none := by
        simp only [Spec.Ffdh.parameterInit]
        rw [ite_eq_right]
        intro h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
        exact hv ⟨h.1.1, h.1.2, h.2⟩
      rw [e, ite_eq_right hv, ite_eq_right hv, cleared_words]
      exact ⟨rfl, rfl⟩

theorem args_out {s : State} (A : ABI s) : ArgsOut 3 s := by
  refine ⟨A.stackBound, fun r hr => ?_⟩
  rw [A.wr] at hr
  obtain rfl := List.mem_singleton.mp hr
  intro a ha hb
  let j := (a - (s.gpr .esp).setWidth 64).toNat
  have hj : j < 16 := by change j + 1 ≤ 16 at ha; omega
  have he : (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 j = a := by
    change (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (a - (s.gpr .esp).setWidth 64).toNat = a
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have a0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by have := A.stackBound; omega)
  by_cases h : j < 4
  · exact A.retOut a (by rw [← he]; exact Offset.contains_base _ (by omega) (by omega)) hb
  · exact A.outArgs a hb (by rw [a0, ← he]; exact Offset.contains _ (by omega) (by omega) (by decide))

theorem constantTime : ConstantTime isa (Spec.Ffdh.parameterInitContract abi).pre
    (Spec.Ffdh.parameterInitContract abi).pub code := by
  refine VG.Taint.constantTime (A := VG.X86.taint) (argTaint [] 16) ?_ (by taint_decide)
  intro s t hs ht H
  sig_pub [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, a0, a1, a2⟩ := H
  refine agree_argTaint (k := 3) (fun _ h => nomatch h) SP (args_out (abi_of hs)) (args_out (abi_of ht)) ?_
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2

/-- The state at `0x1000`, 512 bits and the generator 2, the arguments at `0x4004`. -/
def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 2 else if a = 0x400C then 2 else 0
  rd := [⟨0x4004, 12⟩]
  wr := [⟨0x1000, 128⟩]

theorem satisfiable : ∃ s, (Spec.Ffdh.parameterInitContract abi).pre s := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  have esp : satState.gpr .esp = 0x4000 := rfl
  sig_implies_sat [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig, abi, argSlots, argVal, argBytes,
    stackBelow] [a0, e, esp, satState] using satState

theorem verified : Verified target code (Spec.Ffdh.parameterInitContract abi) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.ParamInit
