module

public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
public import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
meta import VerifiedGarbage.Proof.Dsa.X86.ABIResources
meta import VerifiedGarbage.Impl.Dsa.X86.Generation
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
meta import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
meta import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.EntropyRequest

/-! # `vg_dsa_parameter_search_init` on i686

The width's comparisons with 128, 256 and 384, then `parameterInit`'s words
and the first tape's length `512 p_len` as halves (FFDH's `writes`,
`Proof/Ffdh/X86/ParamInit.lean`), or zeros. Its timing depends only on
`p_len`, a public argument: a taint check. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation.Init
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Dsa.X86.Generation (init initWords initZeros st)
open VG.Impl.Mont.X86 (at_)
open VG.Proof.Ffdh.X86.ParamInit (writes writes_append cleared cleared_words zero_half store_ok zf_eq)
open VG.Proof.Ffdh.X86.KeyInit (read_write_eq read_write_ne)

theorem writes_frame (m : Mem) (B : Addr) :
    ∀ l : List (Nat × BitVec 32), (∀ p ∈ l, p.1 < 8) → Frame [⟨B, 32⟩] m (writes m B l)
  | [] , _ => Frame.refl _ _
  | (j, v) :: l, h => by
    have hj : j < 8 := h (j, v) (List.mem_cons_self ..)
    exact ((Frame.refl [⟨B, 32⟩] m).writeW (List.mem_singleton_self _) v
      (Offset.contains_base B (by omega) (by omega))).trans
      (writes_frame _ B l fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- What the function is given. -/
structure ABI (s : State) : Prop where
  stackBound : (s.gpr .esp).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 8⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 32⟩]
  outArgs : (⟨(arg s 0).setWidth 64, 32⟩ : Region).Disjoint ⟨argAddr s 0, 8⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 32⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 8⟩
  outBound : (arg s 0).toNat + 32 ≤ 2 ^ 32

theorem abi_of {s : State} (h : (Spec.Dsa.parameterInitContract abi).pre s) : ABI s := by
  sig_pre [Spec.Dsa.parameterInitContract, Spec.Dsa.parameterInitSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem ABI.read {s : State} (A : ABI s) {i : Nat} (hi : i < 2) :
    readSrc s (.mem (PublicFn.argument i)) = some (arg s i) :=
  (VG.Proof.Dsa.X86.stackArgument_of (count := 2) (by have := A.stackBound; omega) hi
    (by rw [A.rd]; exact List.mem_append_left _ (List.mem_singleton_self _)) A.outArgs.symm).readSrc

/-- The arguments read the same after stores into the state. -/
theorem ABI.read_after {s u : State} (A : ABI s) {i : Nat} (hi : i < 2) (sp : u.gpr .esp = s.gpr .esp)
    (rd : u.rd = s.rd) (wr : u.wr = s.wr) (F : Frame [⟨(arg s 0).setWidth 64, 32⟩] s.mem u.mem) :
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
  have c : (⟨argAddr s 0, 8⟩ : Region).Contains (s.ea (PublicFn.argument i)) (32 / 8) := by
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

/-- What remains of the code from a state that read the stores so far. -/
structure Cur (s u : State) (l : List (Nat × BitVec 32)) : Prop where
  esp : u.gpr .esp = s.gpr .esp
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mem : u.mem = writes s.mem ((arg s 0).setWidth 64) l
  keeps : Keeps [.eax, .ecx, .edx] s u

theorem Cur.refl (s : State) : Cur s s [] := ⟨rfl, rfl, rfl, rfl, Keeps.refl _ _⟩

theorem Cur.frame {s u : State} {l : List (Nat × BitVec 32)} (C : Cur s u l) (hl : ∀ p ∈ l, p.1 < 8) :
    Frame [⟨(arg s 0).setWidth 64, 32⟩] s.mem u.mem := by
  rw [C.mem]; exact writes_frame _ _ l hl

/-- A store at word `j` with `ecx` the state. -/
theorem Cur.store {is : List Instr} {Q : State → Prop} {s u : State} {l : List (Nat × BitVec 32)} (A : ABI s)
    (C : Cur s u l) (hc : u.gpr .ecx = arg s 0) {r : Reg} {j : Nat} (hj : j < 8)
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

/-- The stores of `initWords L`. -/
def initial (L : Nat) : List (Nat × BitVec 32) :=
  [(0, BitVec.ofNat 32 4096), (2, BitVec.ofNat 32 L), (4, BitVec.ofNat 32 (32769 * L)),
    (6, BitVec.ofNat 32 (512 * L)), (1, 0#32), (3, 0#32), (5, 0#32), (7, 0#32)]

theorem zeros_ok {s u : State} (A : ABI s) (C : Cur s u []) :
    WP isa (.block initZeros) u fun t => t.gpr .eax = 0 ∧ Cur s t cleared := by
  unfold initZeros
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

theorem words_ok {s u : State} (A : ABI s) (C : Cur s u []) (L : Nat) :
    WP isa (.block (initWords L)) u fun t => t.gpr .eax = 1 ∧ Cur s t (initial L) := by
  unfold initWords
  refine wp_movS (A.read_after (by decide) C.esp C.rd C.wr (C.frame (by simp))) fun u1 a1 _ => ?_
  have C1 := C.step a1.keeps (by simp) a1.mem
  have hc : u1.gpr .ecx = arg s 0 := a1.gpr
  refine wp_movS rfl fun u2 a2 _ => ?_
  have C2 := C1.step a2.keeps (by simp) a2.mem
  have hc2 : u2.gpr .ecx = arg s 0 := by rw [a2.other _ (by decide), hc]
  refine C2.store (j := 0) A hc2 (by decide) fun t3 C3 g3 => ?_
  refine wp_movS rfl fun u4 a4 _ => ?_
  have C4 := C3.step a4.keeps (by simp) a4.mem
  have hc4 : u4.gpr .ecx = arg s 0 := by rw [a4.other _ (by decide), g3, hc2]
  refine C4.store (j := 2) A hc4 (by decide) fun t5 C5 g5 => ?_
  refine wp_movS rfl fun u6 a6 _ => ?_
  have C6 := C5.step a6.keeps (by simp) a6.mem
  have hc6 : u6.gpr .ecx = arg s 0 := by rw [a6.other _ (by decide), g5, hc4]
  refine C6.store (j := 4) A hc6 (by decide) fun t7 C7 g7 => ?_
  refine wp_movS rfl fun u8 a8 _ => ?_
  have C8 := C7.step a8.keeps (by simp) a8.mem
  have hc8 : u8.gpr .ecx = arg s 0 := by rw [a8.other _ (by decide), g7, hc6]
  refine C8.store (j := 6) A hc8 (by decide) fun t9 C9 g9 => ?_
  refine wp_movS rfl fun u10 a10 _ => ?_
  have C10 := C9.step a10.keeps (by simp) a10.mem
  have hc10 : u10.gpr .ecx = arg s 0 := by rw [a10.other _ (by decide), g9, hc8]
  refine C10.store (j := 1) A hc10 (by decide) fun t11 C11 g11 => ?_
  refine C11.store (j := 3) A (by rw [g11, hc10]) (by decide) fun t12 C12 g12 => ?_
  refine C12.store (j := 5) A (by rw [g12, g11, hc10]) (by decide) fun t13 C13 g13 => ?_
  refine C13.store (j := 7) A (by rw [g13, g12, g11, hc10]) (by decide) fun t14 C14 g14 => ?_
  refine wp_movS rfl fun t a _ => WP.block_nil ⟨a.gpr, ?_⟩
  have C15 := C14.step a.keeps (by simp) a.mem
  simp only [g13, g12, g11, a10.gpr, a8.gpr, a6.gpr, a4.gpr, a2.gpr, List.nil_append,
    List.cons_append] at C15
  exact C15

/-- The four 64-bit words of `[4096, L, 32769 L, 512 L]`. -/
theorem initial_words (m : Mem) (B : Addr) {L : Nat} (hL : L ≤ 384) :
    Spec.Rsa.wordsAt (writes m B (initial L)) B 4 =
      [4096, L, 32769 * L, 512 * L].map (BitVec.ofNat 64) := by
  rw [VG.Proof.Ffdh.X86.ParamInit.words_halves]
  simp (disch := decide) only [initial, writes, read_write_eq, read_write_ne]
  rw [zero_half (by decide), zero_half (by omega), zero_half (by omega), zero_half (by omega)]
  rfl

/-- What `init` leaves: the status and the stores. -/
def Valid (L : Nat) : Prop := L = 128 ∨ L = 256 ∨ L = 384

instance (L : Nat) : Decidable (Valid L) := by unfold Valid; infer_instance

theorem code_ok {s : State} (A : ABI s) :
    WP isa init s fun t =>
      t.gpr .eax = (if Valid (arg s 1).toNat then 1 else 0) ∧
      Cur s t (if Valid (arg s 1).toNat then initial (arg s 1).toNat else cleared) := by
  have C := Cur.refl s
  have bl := (arg s 1).isLt
  unfold init
  have h1 : WP isa (.block [.mov .edx (.mem (PublicFn.argument 1)), .alu .cmp .edx (.imm 128)]) s
      fun u => u.zf = some (decide ((arg s 1).toNat = 128)) ∧ u.gpr .edx = arg s 1 ∧ Cur s u [] := by
    refine wp_movS (A.read (by decide)) fun u1 a1 _ => ?_
    refine wp_cmpi fun u2 f2 _ z2 => WP.block_nil ⟨?_, by rw [f2.gpr, a1.gpr], ?_⟩
    · rw [z2, a1.gpr]; exact congrArg some (zf_eq (arg s 1) (k := 128) (by decide))
    · exact (C.step a1.keeps (by simp) a1.mem).step (f2.keeps []) (by simp) f2.mem
  refine WP.seq (WP.mono h1 fun u ⟨zu, du, Cu⟩ => ?_)
  refine WP.ite _ zu (fun h => ?_) fun h => ?_
  · have v : Valid (arg s 1).toNat := .inl (of_decide_eq_true h)
    rw [ite_eq_left v, ite_eq_left v, of_decide_eq_true h]
    exact WP.mono (words_ok A Cu 128) fun t ⟨ha, Ct⟩ => ⟨ha, Ct⟩
  have n1 : (arg s 1).toNat ≠ 128 := of_decide_eq_false h
  have h2 : ∀ c : Nat, c < 2 ^ 32 → ∀ {u : State}, u.gpr .edx = arg s 1 → Cur s u [] →
      WP isa (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 c))]) u
      fun u => u.zf = some (decide ((arg s 1).toNat = c)) ∧ u.gpr .edx = arg s 1 ∧ Cur s u [] :=
    fun c hc u du Cu => wp_cmpi fun u2 f2 _ z2 => WP.block_nil ⟨by rw [z2, du]; exact congrArg some (zf_eq _ hc),
      by rw [f2.gpr, du], Cu.step (f2.keeps []) (by simp) f2.mem⟩
  refine WP.seq (WP.mono (h2 256 (by decide) du Cu) fun u ⟨zu, du, Cu⟩ => ?_)
  refine WP.ite _ zu (fun h => ?_) fun h => ?_
  · have v : Valid (arg s 1).toNat := .inr (.inl (of_decide_eq_true h))
    rw [ite_eq_left v, ite_eq_left v, of_decide_eq_true h]
    exact WP.mono (words_ok A Cu 256) fun t ⟨ha, Ct⟩ => ⟨ha, Ct⟩
  have n2 : (arg s 1).toNat ≠ 256 := of_decide_eq_false h
  refine WP.seq (WP.mono (h2 384 (by decide) du Cu) fun u ⟨zu, du, Cu⟩ => ?_)
  refine WP.ite _ zu (fun h => ?_) fun h => ?_
  · have v : Valid (arg s 1).toNat := .inr (.inr (of_decide_eq_true h))
    rw [ite_eq_left v, ite_eq_left v, of_decide_eq_true h]
    exact WP.mono (words_ok A Cu 384) fun t ⟨ha, Ct⟩ => ⟨ha, Ct⟩
  have n3 : (arg s 1).toNat ≠ 384 := of_decide_eq_false h
  have nv : ¬ Valid (arg s 1).toNat := fun h => by rcases h with h | h | h <;> contradiction
  rw [ite_eq_right nv, ite_eq_right nv]
  exact zeros_ok A Cu

theorem final_frame {s t : State} {v : Prop} [Decidable v]
    (C : Cur s t (if v then initial (arg s 1).toNat else cleared)) :
    Frame [⟨(arg s 0).setWidth 64, 32⟩] s.mem t.mem := by
  refine C.frame ?_
  split
  · intro p hp; simp only [initial, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
  · intro p hp; simp only [cleared, List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp; exact hj

theorem correct (s : State) (h : (Spec.Dsa.parameterInitContract abi).pre s) :
    ∃ trace t, Exec isa init s trace t ∧ abiPreserved s t ∧ (Spec.Dsa.parameterInitContract abi).post s t := by
  have A := abi_of h
  obtain ⟨tr, t, E, ha, C⟩ := code_ok A
  refine ⟨tr, t, E, ⟨fun r hr => C.keeps.1 r (by revert r; decide), ?_⟩, ?_⟩
  · exact (final_frame C).readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact A.retOut) (by decide)
  · sig_post [Spec.Dsa.parameterInitContract, Spec.Dsa.parameterInitSig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right, ha, C.mem]
    by_cases hv : Valid (arg s 1).toNat
    · have hL : (arg s 1).toNat ≤ 384 := by rcases hv with h | h | h <;> omega
      have e : Spec.Dsa.parameterInit (arg s 1).toNat =
          some [Spec.Dsa.parameterSeeds, (arg s 1).toNat, Spec.Dsa.parameterEntropy (arg s 1).toNat] := by
        have : Spec.Dsa.generationPLenValid (arg s 1).toNat = true := by
          rcases hv with h | h | h <;> simp [Spec.Dsa.generationPLenValid, h]
        simp only [Spec.Dsa.parameterInit, this, ↓reduceIte]
      rw [e, ite_eq_left hv, ite_eq_left hv, initial_words _ _ hL]
      refine ⟨rfl, 512 * (arg s 1).toNat, rfl, ?_⟩
      have : 0 < (arg s 1).toNat := by rcases hv with h | h | h <;> omega
      exact ⟨by omega, by simp only [Spec.Dsa.parameterEntropy]; omega⟩
    · have e : Spec.Dsa.parameterInit (arg s 1).toNat = none := by
        have : Spec.Dsa.generationPLenValid (arg s 1).toNat = false := by
          simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
          exact ⟨⟨fun h => hv (.inl h), fun h => hv (.inr (.inl h))⟩, fun h => hv (.inr (.inr h))⟩
        simp only [Spec.Dsa.parameterInit, this, Bool.false_eq_true, ↓reduceIte]
      rw [e, ite_eq_right hv, ite_eq_right hv, cleared_words]
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

theorem constantTime : ConstantTime isa (Spec.Dsa.parameterInitContract abi).pre
    (Spec.Dsa.parameterInitContract abi).pub init := by
  refine VG.Taint.constantTime (A := VG.X86.taint) (argTaint [] 12) ?_ (by taint_decide)
  intro s t hs ht H
  sig_pub [Spec.Dsa.parameterInitContract, Spec.Dsa.parameterInitSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, a0, a1⟩ := H
  refine agree_argTaint (k := 2) (fun _ h => nomatch h) SP (args_out (abi_of hs)) (args_out (abi_of ht)) ?_
  intro i hi
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · exact a0
  · exact a1

/-- `state` at `0x1000` and 128 octets, the arguments at `0x4004`. -/
def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4008 then 0x80 else 0
  rd := [⟨0x4004, 8⟩]
  wr := [⟨0x1000, 32⟩]

theorem satisfiable : ∃ s, (Spec.Dsa.parameterInitContract abi).pre s := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  have esp : satState.gpr .esp = 0x4000 := rfl
  sig_implies_sat [Spec.Dsa.parameterInitContract, Spec.Dsa.parameterInitSig, abi, argSlots, argVal, argBytes,
    stackBelow] [a0, e, esp, satState] using satState

theorem init_verified : Verified target init (Spec.Dsa.parameterInitContract abi) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Dsa.X86.Generation.Init
