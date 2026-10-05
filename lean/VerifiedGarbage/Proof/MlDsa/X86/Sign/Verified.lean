import VerifiedGarbage.Impl.MlDsa.X86.Sign.Sign
import VerifiedGarbage.Proof.MlKem.X86.CheckEk
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.MlDsa.Sign.Vals
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlDsa.X86.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits
import VerifiedGarbage.Proof.MlDsa.X86.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86.Round.HintF
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintPack
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.X86.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.X86.Sample.BallTop

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Base`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the setting of the proof

The function is proven as ML-KEM's top-level functions on x86 are
(`Proof/MlKem/X86/Top*.lean`), piece by piece (`Piece`), from the layout of
its arguments (`Y`: `sk`, `mu`, `rnd`, `sig`, `scratch`, and 96 bytes of
stack), with `Ctx` holding between the pieces. Two runs are related (`SPub`)
by the pointers and what signing may leak (`signLeakT`, which is `signLeak`);
a piece of ML-KEM's, whose runs are related by the pointers alone, is one of
these (`lift`).

Blocks whose addresses depend only on `esp` and `esi`, which they do not
write (`esOk`), leak the same in runs that agree on both (`blk_piece`): the
moves of a call's arguments (`setArgs`, `setup_piece`) and the stores to
`scratch`. A loop runs a number of iterations that depends on the initial
state, the same in related runs (`loopN`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The layout and the related runs -/

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := 8 * scratchWords p

/-- The stack signing uses below its return address. -/
abbrev STK : Nat := 96

/-- `sk`, `mu`, `rnd` (read), `sig` and `scratch` (written); 96 bytes of stack. -/
def Y (p : Params) : VG.Proof.MlKem.X86.Top.Lay := ⟨[(p.skLen, false), (64, false), (32, false), (p.sigLen, true), (VG.Proof.MlDsa.X86.Sign.scrLen p, true)], SC, VG.Proof.MlDsa.X86.Sign.STK⟩

/-- Nothing, as the leakage of ML-KEM's pieces. -/
abbrev lk0 : State → List Byte := fun _ => []

section
variable (p : Params) (s₀ : State)
/-- `sk`, `μ` and `rnd`, on entry. -/
abbrev skOf : List Byte := bytesAt s₀.mem (Buf.addr s₀ (bSk 0 p.skLen)) p.skLen
abbrev muOf : List Byte := bytesAt s₀.mem (Buf.addr s₀ bMu) 64
abbrev rndOf : List Byte := bytesAt s₀.mem (Buf.addr s₀ bRnd) 32
end

/-- Two runs with the same pointers and the same leakage. -/
def SPub (p : Params) (s₀ s₀' : State) : Prop :=
  TPub (VG.Proof.MlDsa.X86.Sign.Y p) VG.Proof.MlDsa.X86.Sign.lk0 s₀ s₀' ∧ signLeakT p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) = signLeakT p (VG.Proof.MlDsa.X86.Sign.skOf p s₀') (VG.Proof.MlDsa.X86.Sign.muOf s₀') (VG.Proof.MlDsa.X86.Sign.rndOf s₀')

/-- The pieces of the proof. -/
abbrev SP (p : Params) (A B : State → State → Prop) (c : Prog isa) : Prop := Piece (TPre (VG.Proof.MlDsa.X86.Sign.Y p)) (VG.Proof.MlDsa.X86.Sign.SPub p) A B c

theorem lift {p : Params} {A B : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre (VG.Proof.MlDsa.X86.Sign.Y p)) (TPub (VG.Proof.MlDsa.X86.Sign.Y p) VG.Proof.MlDsa.X86.Sign.lk0) A B c) : VG.Proof.MlDsa.X86.Sign.SP p A B c :=
  h.pre_mono (fun _ h => h) fun _ _ _ _ h => h.1

theorem SPub.t {p : Params} {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') : TPub (VG.Proof.MlDsa.X86.Sign.Y p) VG.Proof.MlDsa.X86.Sign.lk0 s₀ s₀' := h.1

theorem Y_sc (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).sc = SC := rfl

/-! ## Blocks that address through `esp` and `esi` -/

/-- A base register `esp` or `esi`. -/
def esBase (m : MemOp) : Bool := m.base == .esp || m.base == .esi

/-- The addresses of `i` depend only on `esp` and `esi`. -/
def esAddr : Instr → Bool
  | .mov _ (.mem m) | .alu _ _ (.mem m) => VG.Proof.MlDsa.X86.Sign.esBase m
  | .mov .. | .alu .. => true
  | .store m _ | .store8 m _ | .movzx8 _ m => VG.Proof.MlDsa.X86.Sign.esBase m
  | .shift .. | .bswap _ | .mul _ => true
  | .push _ | .pop .. | .alloc _ | .free _ | .movdquLoad .. | .movdquStore .. | .movqLoad .. | .movqStore .. | .xop .. | .mop _ | .mmxStore .. | .mmxEnter | .emms => false

/-- `i` writes neither `esp` nor `esi`, and addresses through them. -/
def esOk (i : Instr) : Bool := !Taint.clobbers i .esp && !Taint.clobbers i .esi && VG.Proof.MlDsa.X86.Sign.esAddr i

theorem esBase_ea {m : MemOp} (h : VG.Proof.MlDsa.X86.Sign.esBase m = true) {s s' : State} (h₁ : s.gpr .esp = s'.gpr .esp)
    (h₂ : s.gpr .esi = s'.gpr .esi) : s.ea m = s'.ea m := by
  simp only [VG.Proof.MlDsa.X86.Sign.esBase, Bool.or_eq_true, beq_iff_eq] at h
  simp only [State.ea]
  rcases h with e | e <;> rw [e] <;> simp only [h₁, h₂]

theorem esAddr_addrs {i : Instr} (h : VG.Proof.MlDsa.X86.Sign.esAddr i = true) {s s' : State} (h₁ : s.gpr .esp = s'.gpr .esp)
    (h₂ : s.gpr .esi = s'.gpr .esi) : addrs i s = addrs i s' := by
  cases i with
  | mov d src =>
    cases src with
    | mem m => simp only [VG.Proof.MlDsa.X86.Sign.esAddr] at h; simp only [addrs, srcAddrs, VG.Proof.MlDsa.X86.Sign.esBase_ea h h₁ h₂]
    | _ => rfl
  | alu op d src =>
    cases src with
    | mem m => simp only [VG.Proof.MlDsa.X86.Sign.esAddr] at h; simp only [addrs, srcAddrs, VG.Proof.MlDsa.X86.Sign.esBase_ea h h₁ h₂]
    | _ => rfl
  | store m r => simp only [VG.Proof.MlDsa.X86.Sign.esAddr] at h; simp only [addrs, VG.Proof.MlDsa.X86.Sign.esBase_ea h h₁ h₂]
  | store8 m r => simp only [VG.Proof.MlDsa.X86.Sign.esAddr] at h; simp only [addrs, VG.Proof.MlDsa.X86.Sign.esBase_ea h h₁ h₂]
  | movzx8 d m => simp only [VG.Proof.MlDsa.X86.Sign.esAddr] at h; simp only [addrs, VG.Proof.MlDsa.X86.Sign.esBase_ea h h₁ h₂]
  | shift | bswap | mul => rfl
  | push | pop | alloc | free | movdquLoad | movdquStore | movqLoad | movqStore | xop | mop | mmxStore | mmxEnter | emms => simp [VG.Proof.MlDsa.X86.Sign.esAddr] at h

theorem esOk_block : ∀ {is : List Instr}, is.all VG.Proof.MlDsa.X86.Sign.esOk = true →
    RelCT isa (fun s s' => s.gpr .esp = s'.gpr .esp ∧ s.gpr .esi = s'.gpr .esi) (.block is) fun _ _ => True := by
  intro is h s₁ s₂ t₁ t₂ s₁' s₂' ⟨e₁, e₂⟩ x₁ x₂
  rw [Exec.block_iff] at x₁ x₂
  refine ⟨?_, trivial⟩
  induction is generalizing s₁ s₂ t₁ t₂ with
  | nil => simp [execBlock] at x₁ x₂; rw [x₁.2, x₂.2]
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases hu₁ : exec i s₁ with
    | none => simp only [execBlock, hu₁] at x₁; cases x₁
    | some u₁ =>
    cases hu₂ : exec i s₂ with
    | none => simp only [execBlock, hu₂] at x₂; cases x₂
    | some u₂ =>
    simp only [execBlock, hu₁, hu₂] at x₁ x₂
    obtain ⟨⟨v₁, w₁⟩, y₁, z₁⟩ := Option.map_eq_some_iff.mp x₁
    obtain ⟨⟨v₂, w₂⟩, y₂, z₂⟩ := Option.map_eq_some_iff.mp x₂
    simp only [Prod.mk.injEq] at z₁ z₂
    rw [← z₁.2, ← z₂.2]
    have hi := h.1
    simp only [VG.Proof.MlDsa.X86.Sign.esOk, Bool.and_eq_true, Bool.not_eq_true'] at hi
    have g₁ := exec_gpr hi.1.1 hu₁
    have g₂ := exec_gpr hi.1.1 hu₂
    have g₃ := exec_gpr hi.1.2 hu₁
    have g₄ := exec_gpr hi.1.2 hu₂
    rw [VG.Proof.MlDsa.X86.Sign.esAddr_addrs hi.2 e₁ e₂,
      ih h.2 u₁ u₂ w₁ w₂ (by rw [g₁, g₂, e₁]) (by rw [g₃, g₄, e₂]) (z₁.1 ▸ y₁) (z₂.1 ▸ y₂)]

/-- A block that addresses through `esp` and `esi`, from `Ctx`. -/
theorem blk_piece {p : Params} {A B : State → State → Prop} {is : List Instr}
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hw : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → WP isa (.block is) s (B s₀)) (h : is.all VG.Proof.MlDsa.X86.Sign.esOk = true) :
    VG.Proof.MlDsa.X86.Sign.SP p A B (.block is) where
  wp := hw
  ct s₀ s₀' hp hp' hq := (VG.Proof.MlDsa.X86.Sign.esOk_block h).mono (fun s s' ⟨a, a'⟩ => by
    have c := hA _ _ hp a
    have c' := hA _ _ hp' a'
    exact ⟨by rw [c.esp, c'.esp, hq.t.E1], by rw [c.esi, c'.esi, hq.t.sc hp]⟩) fun _ _ h => h

/-! ## The moves of a call's arguments -/

/-- The value of an argument. -/
def argV (s₀ : State) : Arg → BitVec 32
  | .buf b => b.ptr s₀
  | .imm v => BitVec.ofNat 32 v

/-- An argument whose buffer lies in its argument. -/
def argOk (Y : VG.Proof.MlKem.X86.Top.Lay) : Arg → Bool
  | .buf b => Y.ok b
  | .imm _ => true

theorem Arg.mov_esOk {d : Reg} (hd : d ≠ .esp) (hd' : d ≠ .esi) (a : Arg) : (a.mov d).all VG.Proof.MlDsa.X86.Sign.esOk = true := by
  cases a with
  | buf b =>
    simp only [Arg.mov, ptrTo]
    split <;> cases d <;> simp_all [VG.Proof.MlDsa.X86.Sign.esOk, VG.Proof.MlDsa.X86.Sign.esAddr, VG.Proof.MlDsa.X86.Sign.esBase, Taint.clobbers, Taint.dst, at_]
  | imm v => cases d <;> simp_all [Arg.mov, VG.Proof.MlDsa.X86.Sign.esOk, VG.Proof.MlDsa.X86.Sign.esAddr, Taint.clobbers, Taint.dst]

theorem setArgs_esOk : ∀ {as : List (Reg × Arg)}, (∀ x ∈ as, x.1 ≠ .esp ∧ x.1 ≠ .esi) →
    (setArgs as).all VG.Proof.MlDsa.X86.Sign.esOk = true
  | [], _ => rfl
  | (d, a) :: as, h => by
    simp only [setArgs, List.all_append, Bool.and_eq_true]
    exact ⟨Arg.mov_esOk (h _ (List.mem_cons_self ..)).1 (h _ (List.mem_cons_self ..)).2 a,
      VG.Proof.MlDsa.X86.Sign.setArgs_esOk fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem argMov_ok {p : Params} {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {d : Reg} {a : Arg}
    (ha : VG.Proof.MlDsa.X86.Sign.argOk (VG.Proof.MlDsa.X86.Sign.Y p) a = true) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = VG.Proof.MlDsa.X86.Sign.argV s₀ a → WP isa (.block is) s' Q) :
    WP isa (.block (a.mov d ++ is)) s Q := by
  cases a with
  | buf b => exact ptrTo_ok hp h ha k
  | imm v => exact VG.Proof.MlKem.X86.Top.wp_movi k

/-- The values of the arguments in their registers. -/
def ArgsAre (s₀ s : State) (as : List Arg) : Prop :=
  ∀ i < as.length, s.gpr (argRegs.getD i .eax) = VG.Proof.MlDsa.X86.Sign.argV s₀ (as.getD i (.imm 0))

theorem setArgs_ok {p : Params} {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) :
    ∀ (as : List (Reg × Arg)) {s : State}, VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s → (as.map Prod.fst).Nodup →
      (∀ x ∈ as, x.1 ≠ .esp ∧ x.1 ≠ .esi ∧ VG.Proof.MlDsa.X86.Sign.argOk (VG.Proof.MlDsa.X86.Sign.Y p) x.2 = true) → ∀ {Q : State → Prop},
      (∀ s', VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → s'.mem = s.mem → (∀ r, r ∉ as.map Prod.fst → s'.gpr r = s.gpr r) →
        (∀ x ∈ as, s'.gpr x.1 = VG.Proof.MlDsa.X86.Sign.argV s₀ x.2) → Q s') →
      WP isa (.block (setArgs as)) s Q
  | [], s, h, _, _, Q, k => WP.block_nil_iff.mpr (k s h rfl (fun _ _ => rfl) fun _ hx => absurd hx List.not_mem_nil)
  | (d, a) :: as, s, h, hnd, hok, Q, k => by
    have h0 := hok _ (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons] at hnd
    unfold setArgs
    refine VG.Proof.MlDsa.X86.Sign.argMov_ok hp h h0.2.2 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by simp [h0.1.symm]) (by simp [h0.2.1.symm])
    refine VG.Proof.MlDsa.X86.Sign.setArgs_ok hp as c₁ hnd.2 (fun x hx => hok x (List.mem_cons_of_mem _ hx)) fun s' c' m' g' v' => ?_
    refine k s' c' (m'.trans o₁.mem) (fun r hr => ?_) fun x hx => ?_
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [g' r hr.2, o₁.gpr r (by simp [hr.1])]
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [g' _ hnd.1, v₁]
      · exact v' x hx

theorem zip_mem {as : List Arg} (hn : as.length ≤ 5) {i : Nat} (hi : i < as.length) :
    (argRegs.getD i .eax, as.getD i (.imm 0)) ∈ argRegs.zip as := by
  have h1 : i < argRegs.length := by simp only [argRegs, List.length_cons, List.length_nil]; omega
  rw [List.mem_iff_getElem]
  refine ⟨i, by simp only [List.length_zip]; omega, ?_⟩
  simp [List.getElem_zip, List.getD_eq_getElem?_getD, hi, List.getElem?_eq_getElem h1]

theorem argRegs_ne : ∀ r ∈ argRegs, r ≠ .esp ∧ r ≠ .esi := by decide

/-- The moves of the arguments `as`. -/
theorem setup_piece' {p : Params} {A : State → State → Prop} (as : List Arg) (hn : as.length ≤ 5)
    (hok : ∀ a ∈ as, VG.Proof.MlDsa.X86.Sign.argOk (VG.Proof.MlDsa.X86.Sign.Y p) a = true) (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) :
    VG.Proof.MlDsa.X86.Sign.SP p A (fun s₀ s₁ => ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s₁ ∧ s₁.mem = s.mem ∧ VG.Proof.MlDsa.X86.Sign.ArgsAre s₀ s₁ as)
      (.block (setArgs (argRegs.zip as))) := by
  have hne : ∀ x ∈ argRegs.zip as, x.1 ≠ .esp ∧ x.1 ≠ .esi := fun x hx => VG.Proof.MlDsa.X86.Sign.argRegs_ne _ (List.of_mem_zip hx).1
  refine VG.Proof.MlDsa.X86.Sign.blk_piece hA (fun s₀ s hp ha => ?_) (VG.Proof.MlDsa.X86.Sign.setArgs_esOk hne)
  refine VG.Proof.MlDsa.X86.Sign.setArgs_ok hp _ (hA _ _ hp ha) ?_ (fun x hx => ⟨(hne x hx).1, (hne x hx).2, hok _ (List.of_mem_zip hx).2⟩)
    fun s' c' m' _ v' => ⟨s, ha, c', m', fun i hi => v' _ (VG.Proof.MlDsa.X86.Sign.zip_mem hn hi)⟩
  match as, hn with
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | [_, _, _, _], _ | [_, _, _, _, _], _ => simp [argRegs]

theorem argPush_len {n : Nat} (hn : n ≤ 5) : (argPush n).length = n := by
  simp only [argPush, List.length_reverse, List.length_take, argRegs, List.length_cons, List.length_nil]; omega

theorem esp_nmem_argPush (n : Nat) : Reg.esp ∉ argPush n := fun h => by
  simp only [argPush, List.mem_reverse] at h
  exact (VG.Proof.MlDsa.X86.Sign.argRegs_ne _ (List.mem_of_mem_take h)).1 rfl

theorem argPush_ne {n : Nat} (hn : 0 < n) : argPush n ≠ [] := by
  cases n with
  | zero => omega
  | succ n => simp [argPush, argRegs]

/-- The callee's argument `i` is the `i`-th argument register. -/
theorem argPush_arg {n : Nat} (hn : n ≤ 5) {s : State} (hfit : 4 * n + 4 ≤ (s.gpr .esp).toNat) {i : Nat}
    (hi : i < n) : arg (pushed (argPush n) s).callEntry i = s.gpr (argRegs.getD i .eax) := by
  have hl := VG.Proof.MlDsa.X86.Sign.argPush_len hn
  rw [callEntry_arg (by rw [hl]; exact hfit) (VG.Proof.MlDsa.X86.Sign.esp_nmem_argPush n) (by rw [hl]; exact hi)]
  congr 1
  have h1 : i < argRegs.length := by simp only [argRegs, List.length_cons, List.length_nil]; omega
  simp only [argPush, List.getElem_reverse, List.getElem_take, hl]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]
  congr 1
  simp only [List.length_take, argRegs, List.length_cons, List.length_nil]
  omega

/-! ## Loops of a number of iterations that depends on the initial state -/

theorem loopN {Pre : State → Prop} {Pub : State → State → Prop} {body : Prog isa} {cnd : Cond}
    (N : State → Nat) (Inv : Nat → State → State → Prop) (hN : ∀ s₀, Pre s₀ → 0 < N s₀)
    (hNp : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → N s₀ = N s₀')
    (hb : ∀ k, Piece Pre Pub (fun s₀ s => Inv k s₀ s ∧ k < N s₀)
      (fun s₀ s => Inv (k + 1) s₀ s ∧ isa.eval cnd s = some (decide (k + 1 < N s₀))) body) :
    Piece Pre Pub (Inv 0) (fun s₀ s => Inv (N s₀) s₀ s) (.loop body cnd) where
  wp s₀ s h₀ ha := by
    refine WP.loop (M := isa) (fun n (s : State) => ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ Inv k s₀ s)
      (fun n s hi => ?_) (N s₀) s ⟨0, (Nat.sub_zero _).symm, hN s₀ h₀, ha⟩
    obtain ⟨k, hn, hk, hi⟩ := hi
    refine ((hb k).wp _ _ h₀ ⟨hi, hk⟩).mono fun s' ⟨hi', hc⟩ => ?_
    by_cases h : k + 1 < N s₀
    · exact .inr ⟨by rw [hc, decide_eq_true h], N s₀ - (k + 1), by omega, k + 1, rfl, h, hi'⟩
    · exact .inl ⟨by rw [hc, decide_eq_false h], by rw [show N s₀ = k + 1 by omega]; exact hi'⟩
  ct s₀ s₀' h₀ h₀' hp := by
    have eN := hNp _ _ h₀ h₀' hp
    have := RelCT.loop (M := isa) (body := body) (c := cnd) (Q := fun _ _ => True)
      (fun n s s' => ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ Inv k s₀ s ∧ Inv k s₀' s')
      (fun n => by
        refine RelCT.exists_ fun k => ?_
        by_cases hk : n = N s₀ - k ∧ k < N s₀
        · refine ((hb k).ct' h₀ h₀' hp).mono (fun s s' ⟨_, _, a, a'⟩ => ⟨⟨a, hk.2⟩, a', eN ▸ hk.2⟩) ?_
          rintro s s' ⟨⟨i₁, c₁⟩, i₂, c₂⟩
          refine ⟨by rw [c₁, c₂, eN], fun _ => trivial, fun h => ?_⟩
          rw [c₁, Option.some.injEq, decide_eq_true_iff] at h
          exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, h, i₁, i₂⟩
        · exact RelCT.of_false fun s s' ⟨h1, h2, _⟩ => hk ⟨h1, h2⟩) (N s₀)
    exact this.mono (fun s s' ⟨a, a'⟩ => ⟨0, (Nat.sub_zero _).symm, hN s₀ h₀, a, a'⟩) fun _ _ h => h

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Call`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): calls

A call (`callP`, `callPR`): the moves of its arguments (`setup_piece'`), then
the call in a frame of its arguments (`Piece.callWith`, `callRet`), as
ML-KEM's `call_piece` makes it but with the runs related by `SPub`, so that a
callee may leak what signing may (`callP_piece`, `callPR_piece`). What the
callee sees on entry: its arguments (`ent_arg`), the stack below `esp`
(`ent_esp`, `ent_arg0`), and the buffers apart from its stack (`ent_rgn`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- What signing needs of a callee's code: it never writes `esp`, and its
calls and frames use at most 56 bytes of stack. -/
structure COk (c : Prog isa) : Prop where
  nosp : NoSp c
  stk : stackUse c ≤ 56

/-- The state after the moves of the arguments `as`, from a state satisfying `A`. -/
def After (p : Params) (A : State → State → Prop) (as : List Arg) (s₀ s₁ : State) : Prop :=
  ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s₁ ∧ s₁.mem = s.mem ∧ VG.Proof.MlDsa.X86.Sign.ArgsAre s₀ s₁ as

/-- The callee's entry state. -/
abbrev ent (n : Nat) (s : State) : State := (pushed (argPush n) s).callEntry

theorem ctx_fit {p : Params} {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {N : Nat} (hN : N ≤ 80) :
    N ≤ (s.gpr .esp).toNat := ctx_E hp h (N := N) (by show N + 16 ≤ 96; omega)

theorem E1_big {p : Params} {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) : 80 ≤ (E1 s₀).toNat := by
  rw [E1_nat s₀ hp.E0_big]; have := hp.sp; simp only [VG.Proof.MlDsa.X86.Sign.Y, VG.Proof.MlDsa.X86.Sign.STK] at this; omega

theorem ent_arg {p : Params} {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {as : List Arg}
    (hn : as.length ≤ 5) (ha : VG.Proof.MlDsa.X86.Sign.ArgsAre s₀ s as) {i : Nat} (hi : i < as.length) :
    arg (VG.Proof.MlDsa.X86.Sign.ent as.length s) i = VG.Proof.MlDsa.X86.Sign.argV s₀ (as.getD i (.imm 0)) := by
  rw [VG.Proof.MlDsa.X86.Sign.argPush_arg hn (VG.Proof.MlDsa.X86.Sign.ctx_fit hp h (by omega)) hi]; exact ha i hi

theorem ent_esp {p : Params} {s₀ s : State} (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {n : Nat} (hn : n ≤ 5) :
    (VG.Proof.MlDsa.X86.Sign.ent n s).gpr .esp = E1 s₀ - BitVec.ofNat 32 (4 * n + 4) := by
  rw [callEntry_esp', h.esp, VG.Proof.MlDsa.X86.Sign.argPush_len hn]

theorem ent_arg0 {p : Params} {s₀ s : State} (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {n : Nat} (hn : n ≤ 5) :
    argAddr (VG.Proof.MlDsa.X86.Sign.ent n s) 0 = (E1 s₀ - BitVec.ofNat 32 (4 * n)).setWidth 64 := by
  rw [callEntry_argAddr0, h.esp, VG.Proof.MlDsa.X86.Sign.argPush_len hn]

theorem ent_frame {p : Params} {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {n : Nat} (hn : n ≤ 5) :
    Frame [below (E1 s₀) (4 * n + 4)] s.mem (VG.Proof.MlDsa.X86.Sign.ent n s).mem := by
  have := callEntry_frame (rs := argPush n) (s := s) (by rw [VG.Proof.MlDsa.X86.Sign.argPush_len hn]; exact VG.Proof.MlDsa.X86.Sign.ctx_fit hp h (by omega))
    (VG.Proof.MlDsa.X86.Sign.esp_nmem_argPush n)
  rw [VG.Proof.MlDsa.X86.Sign.argPush_len hn, h.esp] at this; exact this

/-- A buffer, apart from the callee's arguments, its return address and its stack. -/
theorem ent_rgn {p : Params} {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) {b : Buf} (hb : (VG.Proof.MlDsa.X86.Sign.Y p).ok b = true) {n K : Nat}
    (hK : 4 * n + 4 + K ≤ 80) :
    (b.rgn s₀).Disjoint (below (E1 s₀) (4 * n)) ∧
      (⟨(E1 s₀ - BitVec.ofNat 32 (4 * n + 4)).setWidth 64, 4⟩ : Region).Disjoint (b.rgn s₀) ∧
      (⟨(E1 s₀ - BitVec.ofNat 32 (4 * n + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint (b.rgn s₀) :=
  entry_regions (by have := VG.Proof.MlDsa.X86.Sign.E1_big hp; omega) (Buf.stkD hp hb (N := 4 * n + 4 + K) (by show _ + 16 ≤ 96; omega))

/-- The callee's regions of the stack, apart from its arguments. -/
theorem ent_self {p : Params} {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) {n K : Nat} (hK : 4 * n + 4 + K ≤ 80) :
    (⟨(E1 s₀ - BitVec.ofNat 32 (4 * n + 4)).setWidth 64, 4⟩ : Region).Disjoint (below (E1 s₀) (4 * n)) ∧
      (⟨(E1 s₀ - BitVec.ofNat 32 (4 * n + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint
        (below (E1 s₀) (4 * n)) :=
  entry_self (by have := VG.Proof.MlDsa.X86.Sign.E1_big hp; omega)

/-- The bytes of a buffer, as the callee sees them. -/
theorem ent_bytes {p : Params} {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {n : Nat} (hn : n ≤ 5)
    {b : Buf} (hb : (VG.Proof.MlDsa.X86.Sign.Y p).ok b = true) :
    ∀ i < b.len, (VG.Proof.MlDsa.X86.Sign.ent n s).mem (b.addr s₀ + BitVec.ofNat 64 i) = s.mem (b.addr s₀ + BitVec.ofNat 64 i) :=
  fun _ hi => (VG.Proof.MlDsa.X86.Sign.ent_frame hp h hn).bytes (R := b.rgn s₀)
    (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (Buf.stkD hp hb (N := 4 * n + 4) (by show _ + 16 ≤ 96; omega)).symm)
    (by show b.len ≤ 2 ^ 64; have := Buf.fit hp hb; omega) hi

/-- The callee's argument area is the frame of its arguments, below `esp`. -/
theorem ent_argArea {p : Params} {s₀ s : State} (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {n : Nat} (hn : n ≤ 5) :
    (⟨argAddr (VG.Proof.MlDsa.X86.Sign.ent n s) 0, 4 * n⟩ : Region) = below (E1 s₀) (4 * n) := by
  rw [VG.Proof.MlDsa.X86.Sign.ent_arg0 h hn]

/-- The regions a call writes, and the stack its frame and calls use, within `W`. -/
theorem stk_W {p : Params} {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) {N : Nat} (hN : N ≤ 80) :
    ∃ r' ∈ VG.Proof.MlKem.X86.Top.W (VG.Proof.MlDsa.X86.Sign.Y p) s₀, Region.Sub (below (E1 s₀) N) r' :=
  ⟨cR (VG.Proof.MlDsa.X86.Sign.Y p) s₀, TPre.cW, stk_sub hp hN (by show 80 + 16 ≤ 96; omega)⟩

/-- The callee's regions, within the caller's, for a callee that only reads its arguments. -/
theorem covers_ro {s : State} {n : Nat} {rd : List Region}
    (hrd : ∀ r ∈ rd, r = below (s.gpr .esp) (4 * n) ∨ VG.Proof.MlKem.X86.Within r (s.rd ++ s.wr)) :
    Covers (rd ++ []) (s.rd ++ below (s.gpr .esp) (4 * n) :: s.wr) ∧
      Covers [] (below (s.gpr .esp) (4 * n) :: s.wr) := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => absurd hr List.not_mem_nil⟩
  rw [List.append_nil] at hr
  rcases hrd r hr with rfl | ⟨r', h', o, hb, hl⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), 0, by simp, by simp⟩
  · refine ⟨r', ?_, o, hb, hl⟩
    rcases List.mem_append.mp h' with h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')

/-! ## Calls -/

section
variable {p : Params} {A B : State → State → Prop} {k : Contract isa} {name : String} {c : Prog isa}

/-- A call of verified code in a frame of the arguments `as`, after their moves. -/
theorem callP_piece (as : List Arg) (n : Nat) (hn' : as.length = n) (hv : Verified X86.target c k) (ok : VG.Proof.MlDsa.X86.Sign.COk c)
    (hn0 : 0 < n) (hn : n ≤ 5) (hok : ∀ a ∈ as, VG.Proof.MlDsa.X86.Sign.argOk (VG.Proof.MlDsa.X86.Sign.Y p) a = true) (rd wr : State → List Region)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hk : ∀ s₀ s₁, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → VG.Proof.MlDsa.X86.Sign.After p A as s₀ s₁ → CallPre k (argPush n) (rd s₀) (wr s₀) s₁)
    (hpub : ∀ s₀ s₀' s₁ s₁', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀' → VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀' → VG.Proof.MlDsa.X86.Sign.After p A as s₀ s₁ →
      VG.Proof.MlDsa.X86.Sign.After p A as s₀' s₁' → rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧
        k.pub (((pushed (argPush n) s₁).callEntry).withRegions (rd s₀) (wr s₀))
          (((pushed (argPush n) s₁').callEntry).withRegions (rd s₀) (wr s₀)))
    (hW : ∀ s₀, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → ∀ r ∈ wr s₀, ∃ r' ∈ VG.Proof.MlKem.X86.Top.W (VG.Proof.MlDsa.X86.Sign.Y p) s₀, Region.Sub r r')
    (hQ : ∀ s₀ s₁ s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → VG.Proof.MlDsa.X86.Sign.After p A as s₀ s₁ → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' →
      Frame (wr s₀ ++ [below (E1 s₀) (4 * n + stackUse c + 4)]) s₁.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ k.post (((pushed (argPush n) s₁).callEntry).withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP name c as) := by
  subst hn'
  have hl := VG.Proof.MlDsa.X86.Sign.argPush_len hn
  refine Piece.seq (VG.Proof.MlDsa.X86.Sign.setup_piece' as hn hok hA) ?_
  refine Piece.callWith hv.1 hv.2.1 ok.nosp (VG.Proof.MlDsa.X86.Sign.argPush_ne hn0) (VG.Proof.MlDsa.X86.Sign.esp_nmem_argPush _) rd wr
    (fun s₀ s₁ hp ⟨_, _, h, _⟩ => by rw [hl]; have := ok.stk; exact VG.Proof.MlDsa.X86.Sign.ctx_fit hp h (by omega))
    (fun s₀ s₁ hp ha => hk s₀ s₁ hp ha)
    (fun s₀ s₀' s₁ s₁' hp hp' hq ha ha' => by
      obtain ⟨e₁, e₂, e₃⟩ := hpub s₀ s₀' s₁ s₁' hp hp' hq ha ha'
      obtain ⟨_, _, h, _⟩ := ha
      obtain ⟨_, _, h', _⟩ := ha'
      exact ⟨e₁, e₂, by rw [h.esp, h'.esp, hq.t.E1], e₃⟩)
    (fun s₀ s₁ s' hp ha e₁ e₂ e₃ fr post => ?_)
  have h := ha.choose_spec.2.1
  rw [h.esp, hl] at fr
  refine hQ s₀ s₁ s' hp ha (h.call e₁ e₂ e₃ fr fun r hr => ?_) fr post
  rcases List.mem_append.mp hr with hr | hr
  · exact hW s₀ hp r hr
  · rw [List.mem_singleton] at hr; subst hr; have := ok.stk; exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by omega)

/-- `callP_piece`, for a call that returns a value in `eax`. -/
theorem callPR_piece (as : List Arg) (n : Nat) (hn' : as.length = n) (hv : Verified X86.target c k) (ok : VG.Proof.MlDsa.X86.Sign.COk c)
    (hn0 : 0 < n) (hn : n ≤ 5) (hok : ∀ a ∈ as, VG.Proof.MlDsa.X86.Sign.argOk (VG.Proof.MlDsa.X86.Sign.Y p) a = true) (rd wr : State → List Region)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hk : ∀ s₀ s₁, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → VG.Proof.MlDsa.X86.Sign.After p A as s₀ s₁ → CallPre k (argPush n) (rd s₀) (wr s₀) s₁)
    (hpub : ∀ s₀ s₀' s₁ s₁', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀' → VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀' → VG.Proof.MlDsa.X86.Sign.After p A as s₀ s₁ →
      VG.Proof.MlDsa.X86.Sign.After p A as s₀' s₁' → rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧
        k.pub (((pushed (argPush n) s₁).callEntry).withRegions (rd s₀) (wr s₀))
          (((pushed (argPush n) s₁').callEntry).withRegions (rd s₀) (wr s₀)))
    (hW : ∀ s₀, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → ∀ r ∈ wr s₀, ∃ r' ∈ VG.Proof.MlKem.X86.Top.W (VG.Proof.MlDsa.X86.Sign.Y p) s₀, Region.Sub r r')
    (hQ : ∀ s₀ s₁ s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → VG.Proof.MlDsa.X86.Sign.After p A as s₀ s₁ → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' →
      Frame (wr s₀ ++ [below (E1 s₀) (4 * n + stackUse c + 4)]) s₁.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post (((pushed (argPush n) s₁).callEntry).withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callPR name c as) := by
  subst hn'
  have hl := VG.Proof.MlDsa.X86.Sign.argPush_len hn
  refine Piece.seq (VG.Proof.MlDsa.X86.Sign.setup_piece' as hn hok hA) ?_
  refine Piece.callRet hv.1 hv.2.1 ok.nosp (VG.Proof.MlDsa.X86.Sign.argPush_ne hn0) (VG.Proof.MlDsa.X86.Sign.esp_nmem_argPush _) rd wr
    (fun s₀ s₁ hp ⟨_, _, h, _⟩ => by rw [hl]; have := ok.stk; exact VG.Proof.MlDsa.X86.Sign.ctx_fit hp h (by omega))
    (fun s₀ s₁ hp ha => hk s₀ s₁ hp ha)
    (fun s₀ s₀' s₁ s₁' hp hp' hq ha ha' => by
      obtain ⟨e₁, e₂, e₃⟩ := hpub s₀ s₀' s₁ s₁' hp hp' hq ha ha'
      obtain ⟨_, _, h, _⟩ := ha
      obtain ⟨_, _, h', _⟩ := ha'
      exact ⟨e₁, e₂, by rw [h.esp, h'.esp, hq.t.E1], e₃⟩)
    (fun s₀ s₁ s' hp ha e₁ e₂ e₃ fr post => ?_)
  have h := ha.choose_spec.2.1
  rw [h.esp, hl] at fr
  refine hQ s₀ s₁ s' hp ha (h.call e₁ e₂ e₃ fr fun r hr => ?_) fr post
  rcases List.mem_append.mp hr with hr | hr
  · exact hW s₀ hp r hr
  · rw [List.mem_singleton] at hr; subst hr; have := ok.stk; exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by omega)

end

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Local`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): copies and hashes

A copy of words (`copy_piece`), and SHAKE256 of two buffers (`hash2_piece'`),
as ML-KEM's `copyW_piece` and `hash2_piece`, but with the moves of their
arguments proven constant time by `esOk` rather than the taint analysis, so
that their buffers may be at offsets that depend on the parameter set.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet copyW zeroTop absorbC padC squeezeC hash2)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (Repr bytesAt stateAt squeezeFrom absorb pad rates)

variable {p : Params} {A B : State → State → Prop}

theorem ptrTo_esOk {r : Reg} (h₁ : r ≠ .esp) (h₂ : r ≠ .esi) (b : Buf) : (ptrTo SC r b).all VG.Proof.MlDsa.X86.Sign.esOk = true :=
  Arg.mov_esOk h₁ h₂ (.buf b)

/-- A block that moves arguments into registers, from `Ctx`. -/
theorem setup_es {is : List Instr} (P : State → State → Prop)
    (hw : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s → WP isa (.block is) s fun s₁ => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s₁ ∧ s₁.mem = s.mem ∧ P s₀ s₁)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) (h : is.all VG.Proof.MlDsa.X86.Sign.esOk = true) :
    VG.Proof.MlDsa.X86.Sign.SP p A (fun s₀ s₁ => ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s₁ ∧ s₁.mem = s.mem ∧ P s₀ s₁) (.block is) :=
  VG.Proof.MlDsa.X86.Sign.blk_piece hA (fun s₀ s hp ha => (hw s₀ s hp (hA s₀ s hp ha)).mono fun _ h₁ => ⟨s, ha, h₁⟩) h

theorem copy_piece (sa so da dO n : Nat) (hn : 0 < n) (hn' : n < 2 ^ 30)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨sa, so, 4 * n⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨da, dO, 4 * n⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨sa, so, 4 * n⟩ ⟨da, dO, 4 * n⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' →
      Frame [Buf.rgn s₀ ⟨da, dO, 4 * n⟩] s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ ⟨da, dO, 4 * n⟩) (4 * n) = bytesAt s.mem (Buf.addr s₀ ⟨sa, so, 4 * n⟩) (4 * n) →
      B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (copyW SC ⟨sa, so, 4 * n⟩ ⟨da, dO, 4 * n⟩ n) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, hD⟩, dSD⟩ := hc'
  have hD₁ := (Lay.okW_iff.mp hD).1
  let S : Buf := ⟨sa, so, 4 * n⟩
  let D : Buf := ⟨da, dO, 4 * n⟩
  refine Piece.seq (VG.Proof.MlDsa.X86.Sign.setup_es (fun s₀ s₁ => s₁.gpr .edi = S.ptr s₀ ∧ s₁.gpr .ebp = D.ptr s₀ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n) (fun s₀ s hp h => ?_) hA
      (by simp only [List.all_append, VG.Proof.MlDsa.X86.Sign.ptrTo_esOk (r := .edi) (by decide) (by decide),
        VG.Proof.MlDsa.X86.Sign.ptrTo_esOk (r := .ebp) (by decide) (by decide)]; rfl)) ?_
  · simp only [List.append_assoc]
    refine ptrTo_ok hp h hS fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine ptrTo_ok hp c₁ hD₁ fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₃ o₃ v₃ => WP.block_nil_iff.mpr ?_
    exact ⟨c₂.only o₃ (by decide) (by decide), o₃.mem.trans (o₂.mem.trans o₁.mem),
      by rw [o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁], by rw [o₃.gpr _ (by decide), v₂], v₃⟩
  refine Piece.taint [.edi, .ebp, .ecx] (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃⟩ => ?_)
    (fun s₀ s₀' s s' hp hp' hq ⟨_, _, _, _, e₁, e₂, e₃⟩ ⟨_, _, _, _, e₁', e₂', e₃'⟩ r hr => ?_) (by taint_decide)
  · have fS : (S.ptr s₀).toNat + 4 * n ≤ 2 ^ 32 := Buf.fit hp hS
    have fD : (D.ptr s₀).toNat + 4 * n ≤ 2 ^ 32 := Buf.fit hp hD₁
    have dd := Buf.disj hp hS hD₁ dSD
    let I : Nat → State → Prop := fun k u => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ u ∧ u.gpr .edi = S.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧
      u.gpr .ebp = D.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧ u.gpr .ecx = BitVec.ofNat 32 (n - k) ∧
      Frame [D.rgn s₀] s.mem u.mem ∧ ∀ j < 4 * k, u.mem (D.addr s₀ + BitVec.ofNat 64 j) = s.mem (S.addr s₀ + BitVec.ofNat 64 j)
    have i0 : I 0 s₁ := ⟨h₁, by rw [e₁]; simp, by rw [e₂]; simp, e₃, by rw [m₁]; exact Frame.refl _ _,
      fun j hj => absurd hj (by omega)⟩
    refine (wp_count hn I i0 fun k hk u ⟨cu, du, bu, xu, fu, cpu⟩ => ?_).mono fun u ⟨cu, _, _, _, fu, cpu⟩ => ?_
    · have eS : u.ea (at_ .edi 0) = S.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, du]; rw [ea_add (by omega)]; rfl
      have eD : u.ea (at_ .ebp 0) = D.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, bu]; rw [ea_add (by omega)]; rfl
      have hinS : InRegions (u.rd ++ u.wr) (S.addr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
        Buf.inRegR hp hS cu.rd cu.wr (show 4 * k + 4 ≤ 4 * n by omega)
      refine wp_movm' (by rw [eS]; exact hinS) fun u₁ o₁ v₁ => ?_
      have c₁ := cu.only o₁ (by decide) (by decide)
      have eD₁ : u₁.ea (at_ .ebp 0) = D.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        rw [← eD]; simp only [State.ea, at_, o₁.gpr _ (by decide : Reg.ebp ∉ [Reg.eax])]
      have hinD : InRegions u₁.wr (D.addr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
        Buf.inRegW hp hD₁ (Lay.okW_iff.mp hD).2 c₁.wr (show 4 * k + 4 ≤ 4 * n by omega)
      refine wp_store' (by rw [eD₁]; exact hinD) fun u₂ g₂ r₂ w₂ m₂ => ?_
      obtain ⟨r, hr, hcr⟩ := Buf.contains hp hD₁ (Lay.okW_iff.mp hD).2 (o := 4 * k) (n := 4)
        (show 4 * k + 4 ≤ 4 * n by omega)
      have c₂ : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ u₂ := ⟨by rw [g₂]; exact c₁.esp, by rw [r₂]; exact c₁.rd, by rw [w₂]; exact c₁.wr,
        by rw [g₂]; exact c₁.esi, by rw [m₂, eD₁]; exact c₁.frame.writeW hr _ hcr⟩
      refine wp_addi fun u₃ o₃ v₃ => wp_addi fun u₄ o₄ v₄ => wp_subi_last fun u₅ o₅ v₅ z₅ => ?_
      have c₅ := ((c₂.only o₃ (by decide) (by decide)).only o₄ (by decide) (by decide)).only o₅ (by decide)
        (by decide)
      have m₅ : u₅.mem = u₁.mem.writeW (D.addr s₀ + BitVec.ofNat 64 (4 * k)) (u.mem.readW (S.addr s₀ +
          BitVec.ofNat 64 (4 * k)) 32) := by
        rw [o₅.mem, o₄.mem, o₃.mem, m₂, eD₁, v₁, eS]
      have ex : u₄.gpr .ecx = BitVec.ofNat 32 (n - k) := by
        rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), g₂, o₁.gpr _ (by decide), xu]
      refine ⟨⟨c₅, ?_, ?_, by rw [v₅, ex]; exact cnt_next hk, ?_, ?_⟩, ?_⟩
      · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃, g₂, o₁.gpr _ (by decide), du]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
      · rw [o₅.gpr _ (by decide), v₄, o₃.gpr _ (by decide), g₂, o₁.gpr _ (by decide), bu]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
      · rw [m₅, o₁.mem]
        exact fu.writeW (List.mem_singleton_self _) _ (by
          show (⟨D.addr s₀, 4 * n⟩ : Region).Contains _ 4
          simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      · intro j hj
        rw [m₅, o₁.mem, wordw_bytes (by omega) hj]
        split
        · rename_i e
          rw [← Mem.readW_byte _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
            show 4 * k + (j - 4 * k) = j by omega]
          exact fu.bytes (R := S.rgn s₀) (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact dd) (by show 4 * n ≤ 2 ^ 64; omega)
            (show j < 4 * n by omega)
        · exact cpu j (by omega)
      · show u₅.zf.map (!·) = _
        rw [z₅, ex]; exact cnt_ne hk (by omega)
    · refine hQ s₀ s u hp ha cu fu ?_
      exact List.map_congr_left fun j hj => cpu j (List.mem_range.mp hj)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁, e₁', hq.t.ptr hS]
    · rw [e₂, e₂', hq.t.ptr hD₁]
    · rw [e₃, e₃']


theorem absorbC_piece' (st wk rate pos : Nat) (b : Buf) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, st, 200⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, wk, 640⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).ok b && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨SC, st, 200⟩ ⟨SC, wk, 640⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep b ⟨SC, st, 200⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep b ⟨SC, wk, 640⟩) = true)  (hlen : b.len < 2 ^ 32)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' →
      Frame ([⟨SC, st, 200⟩, ⟨SC, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨SC, st, 200⟩) rate msg → pos = msg.length % rate →
        Repr s'.mem (Buf.addr s₀ ⟨SC, st, 200⟩) rate (msg ++ bytesAt s.mem (b.addr s₀) b.len)) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (absorbC SC st wk rate pos b) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (VG.Proof.MlDsa.X86.Sign.setup_es (fun s₀ s₁ => AbsArgs s₁ (Buf.ptr s₀ ⟨SC, st, 200⟩) (b.ptr s₀)
      (Buf.ptr s₀ ⟨SC, wk, 640⟩) rate pos b.len) (fun s₀ s hp h => ?_) hA (by simp only [List.all_append, VG.Proof.MlDsa.X86.Sign.ptrTo_esOk (r := .eax) (by decide) (by decide), VG.Proof.MlDsa.X86.Sign.ptrTo_esOk (r := .ebx) (by decide) (by decide), VG.Proof.MlDsa.X86.Sign.ptrTo_esOk (r := .edi) (by decide) (by decide)]; rfl))
    (VG.Proof.MlDsa.X86.Sign.lift (VG.Proof.MlKem.X86.Top.absorb_call (Y := VG.Proof.MlDsa.X86.Sign.Y p) SC st SC wk b rate pos hr hpos hc (show 56 ≤ 96 by decide) hlen (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₂ o₂ v₂ => VG.Proof.MlKem.X86.Top.wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := (c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)
    refine ptrTo_ok hp c₃ h2 fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₅ o₅ v₅ => ?_
    have c₅ := c₄.only o₅ (by decide) (by decide)
    rw [← List.append_nil (ptrTo SC .edi _)]
    refine ptrTo_ok hp c₅ (Lay.okW_iff.mp h1).1 fun s₆ o₆ v₆ => WP.block_nil_iff.mpr ?_
    refine ⟨c₅.only o₆ (by decide) (by decide),
      o₆.mem.trans (o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)))), ⟨?_, ?_, ?_, ?_, ?_, v₆⟩⟩
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
        o₂.gpr _ (by decide), v₁]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), v₄]
    · rw [o₆.gpr _ (by decide), v₅]
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem padC_piece' (st wk rate pos sfx : Nat) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, st, 200⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, wk, 640⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨SC, st, 200⟩ ⟨SC, wk, 640⟩) = true)

    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' →
      Frame ([⟨SC, st, 200⟩, ⟨SC, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨SC, st, 200⟩) rate msg → pos = msg.length % rate →
        stateAt s'.mem (Buf.addr s₀ ⟨SC, st, 200⟩) =
          absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg)) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (padC SC st wk rate pos sfx) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (VG.Proof.MlDsa.X86.Sign.setup_es (fun s₀ s₁ => PadArgs s₁ (Buf.ptr s₀ ⟨SC, st, 200⟩)
      (Buf.ptr s₀ ⟨SC, wk, 640⟩) rate pos sfx) (fun s₀ s hp h => ?_) hA (by simp only [List.all_append, VG.Proof.MlDsa.X86.Sign.ptrTo_esOk (r := .eax) (by decide) (by decide), VG.Proof.MlDsa.X86.Sign.ptrTo_esOk (r := .edi) (by decide) (by decide)]; rfl))
    (VG.Proof.MlDsa.X86.Sign.lift (VG.Proof.MlKem.X86.Top.pad_call (Y := VG.Proof.MlDsa.X86.Sign.Y p) SC st SC wk rate pos sfx hr hpos hc (show 56 ≤ 96 by decide) (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₂ o₂ v₂ => VG.Proof.MlKem.X86.Top.wp_movi fun s₃ o₃ v₃ => VG.Proof.MlKem.X86.Top.wp_movi fun s₄ o₄ v₄ => ?_
    have c₄ := ((c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)).only o₄ (by decide)
      (by decide)
    rw [← List.append_nil (ptrTo SC .edi _)]
    refine ptrTo_ok hp c₄ (Lay.okW_iff.mp h1).1 fun s₅ o₅ v₅ => WP.block_nil_iff.mpr ?_
    refine ⟨c₄.only o₅ (by decide) (by decide),
      o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem))), ⟨?_, ?_, ?_, ?_, v₅⟩⟩
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]
    · rw [o₅.gpr _ (by decide), v₄]
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem squeezeC_piece' (st wk rate : Nat) (o : Buf) (hr : rate ∈ rates)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, st, 200⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, wk, 640⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW o && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨SC, st, 200⟩ ⟨SC, wk, 640⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨SC, st, 200⟩ o && (VG.Proof.MlDsa.X86.Sign.Y p).sep o ⟨SC, wk, 640⟩) = true)  (hlen : o.len < 2 ^ 32)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' →
      Frame ([⟨SC, st, 200⟩, o, ⟨SC, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len =
        squeezeFrom rate (stateAt s.mem (Buf.addr s₀ ⟨SC, st, 200⟩)) 0 o.len → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (squeezeC SC st wk rate o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (VG.Proof.MlDsa.X86.Sign.setup_es (fun s₀ s₁ => AbsArgs s₁ (Buf.ptr s₀ ⟨SC, st, 200⟩) (o.ptr s₀)
      (Buf.ptr s₀ ⟨SC, wk, 640⟩) rate 0 o.len) (fun s₀ s hp h => ?_) hA (by simp only [List.all_append, VG.Proof.MlDsa.X86.Sign.ptrTo_esOk (r := .eax) (by decide) (by decide), VG.Proof.MlDsa.X86.Sign.ptrTo_esOk (r := .ebx) (by decide) (by decide), VG.Proof.MlDsa.X86.Sign.ptrTo_esOk (r := .edi) (by decide) (by decide)]; rfl))
    (VG.Proof.MlDsa.X86.Sign.lift (VG.Proof.MlKem.X86.Top.squeeze_call (Y := VG.Proof.MlDsa.X86.Sign.Y p) SC st SC wk o rate 0 hr (Nat.zero_le _) hc (show 56 ≤ 96 by decide) hlen
      (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr r₁ _ => ?_))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₂ o₂ v₂ => VG.Proof.MlKem.X86.Top.wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := (c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)
    refine ptrTo_ok hp c₃ (Lay.okW_iff.mp h2).1 fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₅ o₅ v₅ => ?_
    have c₅ := c₄.only o₅ (by decide) (by decide)
    rw [← List.append_nil (ptrTo SC .edi _)]
    refine ptrTo_ok hp c₅ (Lay.okW_iff.mp h1).1 fun s₆ o₆ v₆ => WP.block_nil_iff.mpr ?_
    refine ⟨c₅.only o₆ (by decide) (by decide),
      o₆.mem.trans (o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)))), ⟨?_, ?_, ?_, ?_, ?_, v₆⟩⟩
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
        o₂.gpr _ (by decide), v₁]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]; rfl
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), v₄]
    · rw [o₆.gpr _ (by decide), v₅]
  · rw [m₁] at fr r₁
    exact hQ s₀ s s' hp ha h' fr r₁

/-- The SHA-3 or SHAKE function (`rate`, suffix `sfx`) of the bytes of `b₁` and `b₂`, into `o`. -/
theorem hash2_piece' (rate sfx : Nat) (b₁ b₂ o : Buf) (hr : rate ∈ rates)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, oST, 200⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, oWK, 640⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).ok b₁ && (VG.Proof.MlDsa.X86.Sign.Y p).ok b₂ && (VG.Proof.MlDsa.X86.Sign.Y p).okW o &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨SC, oST, 200⟩ ⟨SC, oWK, 640⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep b₁ ⟨SC, oST, 200⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep b₁ ⟨SC, oWK, 640⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep b₂ ⟨SC, oST, 200⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep b₂ ⟨SC, oWK, 640⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨SC, oST, 200⟩ o &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep o ⟨SC, oWK, 640⟩) = true)
    (hl₁ : b₁.len < 2 ^ 32) (hl₂ : b₂.len < 2 ^ 32) (hlo : o.len < 2 ^ 32)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' →
      Frame ([⟨SC, oST, 200⟩, ⟨SC, oWK, 640⟩, o].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len = squeezeFrom rate (absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
        (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len))) 0 o.len → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (hash2 SC oST oWK rate sfx b₁ b₂ o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hW⟩, hb₁⟩, hb₂⟩, hO⟩, dSW⟩, d₁S⟩, d₁W⟩, d₂S⟩, d₂W⟩, dSO⟩, dOW⟩ := hc'
  have hrate := (rate_lt hr)
  have hr0 : 0 < rate := by simp [rates] at hr; omega
  -- after zeroing, absorbing `b₁`, absorbing `b₂`, padding
  let P : Nat → State → State → Prop := fun i s₀ u => ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ u ∧ Frame (kF oST oWK (VG.Proof.MlDsa.X86.Sign.Y p) s₀) s.mem u.mem ∧
    (i = 0 → stateAt u.mem (Buf.addr s₀ ⟨SC, oST, 200⟩) = Spec.Sha3.zero) ∧
    (i = 1 → Repr u.mem (Buf.addr s₀ ⟨SC, oST, 200⟩) rate (bytesAt s.mem (b₁.addr s₀) b₁.len)) ∧
    (i = 2 → Repr u.mem (Buf.addr s₀ ⟨SC, oST, 200⟩) rate
      (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len)) ∧
    (i = 3 → stateAt u.mem (Buf.addr s₀ ⟨SC, oST, 200⟩) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
      (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len)))
  have cS : ((VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, oST, 200⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, oWK, 640⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨SC, oST, 200⟩ ⟨SC, oWK, 640⟩) = true := by
    simp [hS, hW, dSW]
  refine Piece.seq (B := P 0) (VG.Proof.MlDsa.X86.Sign.lift (zeroTop_piece (Y := VG.Proof.MlDsa.X86.Sign.Y p) oST hS (by taint_decide) hA fun s₀ s s' hp ha h' fr z =>
    ⟨s, ha, h', kF_zero hp (show 56 ≤ 96 by decide) fr, fun _ => z, by simp, by simp, by simp⟩)) ?_
  refine Piece.seq (B := P 1) (VG.Proof.MlDsa.X86.Sign.absorbC_piece' oST oWK rate 0 b₁ hr hr0 (by simp [hS, hW, hb₁, dSW, d₁S, d₁W])
    hl₁ (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, z, _⟩ h' fr post => ?_) ?_
  · have r := post [] (repr_nil (z rfl)) (by simp)
    rw [List.nil_append, kF_bytes hp (show 56 ≤ 96 by decide) hb₁ (by simp [VG.Proof.MlDsa.X86.Sign.Y_sc, hS, hW, d₁S, d₁W]) fu] at r
    exact ⟨s, ha, h', fu.trans fr, by simp, fun _ => r, by simp, by simp⟩
  refine Piece.seq (B := P 2) (VG.Proof.MlDsa.X86.Sign.absorbC_piece' oST oWK rate (b₁.len % rate) b₂ hr (Nat.mod_lt _ hr0)
    (by simp [hS, hW, hb₂, dSW, d₂S, d₂W]) hl₂ (fun s₀ u _ ⟨_, _, h, _⟩ => h)
    fun s₀ u u' hp ⟨s, ha, _, fu, _, r, _⟩ h' fr post => ?_) ?_
  · have r' := post _ (r rfl) (by rw [bytesAt_length])
    rw [kF_bytes hp (show 56 ≤ 96 by decide) hb₂ (by simp [VG.Proof.MlDsa.X86.Sign.Y_sc, hS, hW, d₂S, d₂W]) fu] at r'
    exact ⟨s, ha, h', fu.trans fr, by simp, by simp, fun _ => r', by simp⟩
  refine Piece.seq (B := P 3) (VG.Proof.MlDsa.X86.Sign.padC_piece' oST oWK rate ((b₁.len + b₂.len) % rate) sfx hr (Nat.mod_lt _ hr0) cS
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, r, _⟩ h' fr post => ?_) ?_
  · exact ⟨s, ha, h', fu.trans fr, by simp, by simp, by simp,
      fun _ => post _ (r rfl) (by rw [List.length_append, bytesAt_length, bytesAt_length])⟩
  refine VG.Proof.MlDsa.X86.Sign.squeezeC_piece' oST oWK rate o hr (by simp [hS, hW, hO, dSW, dSO, dOW]) hlo
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, _, z⟩ h' fr r₁ => ?_
  rw [z rfl] at r₁
  refine hQ s₀ s u' hp ha h' ((fu.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)) r₁
  · simp only [kF, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp [VG.Proof.MlDsa.X86.Sign.Y_sc], fun _ h => h⟩
  · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Params`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the parameter sets, and the layout

What the proofs need of a parameter set (`PS`), which the three parameter sets
have (`PS.of`); and the layout as numbers (`Y_n`, `Y_alen0`, …), from which
the tactic `ofs` (`Inv.lean`) proves the layout checks of a call by `omega`.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa

/-- The three parameter sets. -/
def Ok3 (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

/-- What the proofs need of a parameter set. -/
structure PS (p : Params) : Prop where
  hk : 4 ≤ p.k ∧ p.k ≤ 8
  hl : 4 ≤ p.ℓ ∧ p.ℓ ≤ 7
  hsLen : sLen p = 96 ∨ sLen p = 128
  hskLen : p.skLen = 128 + sLen p * (p.ℓ + p.k) + 416 * p.k
  hcLen : cLen p = 32 ∨ cLen p = 48 ∨ cLen p = 64
  hzLen : zLen p = 576 ∨ zLen p = 640
  hsigLen : p.sigLen = cLen p + zLen p * p.ℓ + p.ω + p.k
  hw1 : p.k * w1Len p ≤ 1024
  hw1Len : w1Len p = 128 ∨ w1Len p = 192
  hω : p.ω ≤ 80
  hhint : (p.ω, p.k) ∈ hintParams
  hball : (cLen p, p.τ) ∈ ballParams
  hγ₁ : p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19
  hγ₂ : p.γ₂ ∈ gamma2s
  hη : (p.η, p.η) ∈ bitPackParams ∧ sLen p = 32 * bitlen (p.η + p.η) ∧ p.η < 2 ^ 32
  hz : (p.γ₁ - 1, p.γ₁) ∈ bitPackParams ∧ zLen p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)
  ht0 : ((4095 : Nat), (4096 : Nat)) ∈ bitPackParams ∧ 416 = 32 * bitlen (4095 + 4096)
  hw1Max : w1Max p ∈ simpleBitPackBounds ∧ w1Len p = 32 * bitlen (w1Max p)
  hok : ParamsOk p
  hβ : 1 ≤ p.β ∧ p.β < p.γ₂ ∧ p.γ₁ < 2 ^ 20 ∧ p.γ₂ < 2 ^ 20
  hscr : VG.Proof.MlDsa.X86.Sign.scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32)

theorem PS.of {p : Params} (h : VG.Proof.MlDsa.X86.Sign.Ok3 p) : VG.Proof.MlDsa.X86.Sign.PS p := by
  rcases h with rfl | rfl | rfl <;>
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel, rfl⟩

/-- The layout, as numbers. -/
theorem Y_n (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).n = 5 := rfl
theorem Y_alen0 (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).alen 0 = p.skLen := rfl
theorem Y_alen1 (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).alen 1 = 64 := rfl
theorem Y_alen2 (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).alen 2 = 32 := rfl
theorem Y_alen3 (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).alen 3 = p.sigLen := rfl
theorem Y_alen4 (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).alen 4 = VG.Proof.MlDsa.X86.Sign.scrLen p := rfl
theorem Y_awr0 (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).awr 0 = false := rfl
theorem Y_awr1 (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).awr 1 = false := rfl
theorem Y_awr2 (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).awr 2 = false := rfl
theorem Y_awr3 (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).awr 3 = true := rfl
theorem Y_awr4 (p : Params) : (VG.Proof.MlDsa.X86.Sign.Y p).awr 4 = true := rfl

theorem Lay.sep_iff {Y : VG.Proof.MlKem.X86.Top.Lay} {b c : Buf} : Y.sep b c = true ↔
    (b.arg = c.arg ∧ (b.off + b.len ≤ c.off ∨ c.off + c.len ≤ b.off)) ∨
      (b.arg ≠ c.arg ∧ (Y.awr b.arg = true ∨ Y.awr c.arg = true)) := by
  unfold Lay.sep
  split <;> simp_all

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Blocks`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the blocks between calls

Loads and stores of words and bytes of `scratch` from `Ctx` (`wp_ldsc`,
`wp_stsc`, `wp_st8sc`), and the pieces made of them: sequences (`seqR_piece`),
the empty block (`nil_piece`), and the branch on `OK` (`okIte_piece`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {A B : State → State → Prop}

/-- The word of `scratch` at `o`. -/
abbrev scw (s₀ s : State) (o : Nat) : BitVec 32 := s.mem.readW (Buf.addr s₀ (sc o 4)) 32

theorem ea_sc {s₀ s : State} (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) (o : Nat) (n : Nat) :
    s.ea (at_ .esi o) = Buf.addr s₀ (sc o n) := by
  simp only [State.ea, at_]; rw [h.esi]; rfl

/-- `r ← ` the word of `scratch` at `o`. -/
theorem wp_ldsc {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {o : Nat} (hc : (VG.Proof.MlDsa.X86.Sign.Y p).ok (sc o 4) = true)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [r] s s' → s'.gpr r = VG.Proof.MlDsa.X86.Sign.scw s₀ s o → WP isa (.block is) s' Q) :
    WP isa (.block (.mov r (.mem (at_ .esi o)) :: is)) s Q := by
  have hin : InRegions (s.rd ++ s.wr) (Buf.addr s₀ (sc o 4)) 4 := by
    have := Buf.inRegR hp hc h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  exact wp_movm' (by rw [VG.Proof.MlDsa.X86.Sign.ea_sc h o 4]; exact hin) fun s' o' v' => k s' o' (by rw [v', VG.Proof.MlDsa.X86.Sign.ea_sc h o 4])

theorem ctx_write {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {o n w : Nat} (hc : (VG.Proof.MlDsa.X86.Sign.Y p).okW (sc o n) = true)
    (hw : w / 8 ≤ n) (v : BitVec w) : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ { s with
                                                            mem := s.mem.writeW (Buf.addr s₀ (sc o n)) v } := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := w / 8) (by show 0 + w / 8 ≤ n; omega)
  rw [BitVec.add_zero] at hcr
  exact ⟨h.esp, h.rd, h.wr, h.esi, h.frame.writeW hr _ hcr⟩

/-- The word of `scratch` at `o` ← `r`. -/
theorem wp_stsc {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {o : Nat} (hc : (VG.Proof.MlDsa.X86.Sign.Y p).okW (sc o 4) = true)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → (∀ x, s'.gpr x = s.gpr x) → s'.mem = s.mem.writeW (Buf.addr s₀ (sc o 4)) (s.gpr r) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ .esi o) r :: is)) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  have hin : InRegions s.wr (Buf.addr s₀ (sc o 4)) 4 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  refine wp_store' (by rw [VG.Proof.MlDsa.X86.Sign.ea_sc h o 4]; exact hin) fun s' g' r' w' m' => ?_
  rw [VG.Proof.MlDsa.X86.Sign.ea_sc h o 4] at m'
  have c := VG.Proof.MlDsa.X86.Sign.ctx_write hp h hc (w := 32) (by decide) (s.gpr r)
  exact k s' ⟨by rw [g']; exact c.esp, by rw [r']; exact c.rd, by rw [w']; exact c.wr, by rw [g']; exact c.esi,
    by rw [m']; exact c.frame⟩ g' m'

/-- The byte of `scratch` at `o` ← the low byte of `r`. -/
theorem wp_st8sc {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {o : Nat} (hc : (VG.Proof.MlDsa.X86.Sign.Y p).okW (sc o 1) = true)
    {r : Reg8} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → (∀ x, s'.gpr x = s.gpr x) →
      s'.mem = s.mem.writeW (Buf.addr s₀ (sc o 1)) ((s.gpr r.reg).setWidth 8) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 (at_ .esi o) r :: is)) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  have hin : InRegions s.wr (Buf.addr s₀ (sc o 1)) 1 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 1) (Nat.le_refl _)
    simpa using this
  refine wp_store8 (by rw [VG.Proof.MlDsa.X86.Sign.ea_sc h o 1]; exact hin) ?_
  rw [VG.Proof.MlDsa.X86.Sign.ea_sc h o 1]
  exact k _ (VG.Proof.MlDsa.X86.Sign.ctx_write hp h hc (w := 8) (by decide) _) (fun _ => rfl) rfl

theorem wp_addr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d + s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d + s.gpr r) (decide (2 ^ 32 ≤ (s.gpr d).toNat + (s.gpr r).toNat))
      (addOverflow (s.gpr d) (s.gpr r) (s.gpr d + s.gpr r))).setReg d (s.gpr d + s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_test {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [] s s' → s'.zf = some (s.gpr r &&& s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test r (.reg r) :: is)) s Q :=
  wp_cons (s' := arithFlags s (s.gpr r &&& s.gpr r) false false)
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_subi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - v → s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat))
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]) rfl)

/-! ## Pieces -/

/-- The empty block. -/
theorem nil_piece (h : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → B s₀ s) : VG.Proof.MlDsa.X86.Sign.SP p A B (.block []) where
  wp s₀ s hp ha := WP.block_nil_iff.mpr (h s₀ s hp ha)
  ct _ _ _ _ _ := fun _ _ _ _ _ _ _ e₁ e₂ => by
    rw [Exec.block_iff] at e₁ e₂
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    exact ⟨e₁.2.symm.trans e₂.2, trivial⟩

/-- `f a, …, f (a + n - 1)`, from pieces for each. -/
theorem seqR_piece {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (a n : Nat), (∀ i, a ≤ i → i < a + n → VG.Proof.MlDsa.X86.Sign.SP p (I i) (I (i + 1)) (f i)) → VG.Proof.MlDsa.X86.Sign.SP p (I a) (I (a + n)) (seqR f a n)
  | a, 0, _ => VG.Proof.MlDsa.X86.Sign.nil_piece fun _ _ _ h => h
  | a, n + 1, h => by
    refine Piece.seq (h a (Nat.le_refl _) (by omega)) ?_
    have := VG.Proof.MlDsa.X86.Sign.seqR_piece (I := I) (a + 1) n fun i hi hi' => h i (by omega) (by omega)
    rwa [show a + 1 + n = a + (n + 1) by omega] at this

/-- The branch on `OK`, which is 1 or 0 as `b` of the initial state says. -/
theorem okIte_piece (hc : (VG.Proof.MlDsa.X86.Sign.Y p).ok (sc oOK 4) = true) {t e : Prog isa} (b : State → Bool)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = if b s₀ then 1 else 0)
    (hb : ∀ s₀ s₀', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀' → VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀' → b s₀ = b s₀')
    (ht : VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s₁ => (∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧ b s₀ = true) B t)
    (he : VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s₁ => (∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧ b s₀ = false) B e) :
    VG.Proof.MlDsa.X86.Sign.SP p A B (ifOkElse t e) := by
  refine Piece.seq (B := fun s₀ s₁ => (∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧
    s₁.zf = some (!b s₀)) (VG.Proof.MlDsa.X86.Sign.blk_piece (fun s₀ s hp ha => (hA s₀ s hp ha).1) (fun s₀ s hp ha => ?_) rfl) ?_
  · obtain ⟨h, hok⟩ := hA s₀ s hp ha
    refine VG.Proof.MlDsa.X86.Sign.wp_ldsc hp h hc fun s₁ o₁ v₁ => VG.Proof.MlDsa.X86.Sign.wp_test fun s₂ o₂ z₂ => WP.block_nil_iff.mpr ?_
    have o := o₁.trans o₂
    refine ⟨⟨s, ha, h.only o (by simp) (by simp), o.mem⟩, ?_⟩
    rw [z₂, v₁, hok]
    cases b s₀ <;> rfl
  · refine Piece.ite b (fun s₀ s₁ hp ha => ?_) hb (ht.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
      (he.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
    show s₁.zf.map (!·) = _
    rw [ha.2]; cases b s₀ <;> rfl

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Inv`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): what the pieces keep

The slots of polynomials (`nS` of them, `slot_ok`), families of consecutive
slots (`Fam`), and what a piece that writes the buffers `bs` keeps: the frame
of each call is widened to a few large buffers (`frIn`), so that what a whole
phase keeps is shown once (`Fam.keep`, `keepB`, `keepW'`). The tactic `ofs`
proves the arithmetic of offsets from the facts of `PS p`.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlKem.X86 (sub_of_contains contains_at)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The slot of `Â[0, 0]`. -/
abbrev aBase (p : Params) : Nat := 5 + 4 * p.k + 3 * p.ℓ

/-- The number of slots of polynomials. -/
abbrev nS (p : Params) : Nat := 5 + 4 * p.k + 3 * p.ℓ + p.k * p.ℓ

variable {p : Params}

/-! ## Buffers within buffers -/

/-- `c` lies within `d`. -/
def In (c d : Buf) : Prop := c.arg = d.arg ∧ d.off ≤ c.off ∧ c.off + c.len ≤ d.off + d.len

theorem rgn_sub {Y : VG.Proof.MlKem.X86.Top.Lay} {s₀ : State} (hp : TPre Y s₀) {c d : Buf} (hc : Y.ok c = true) (hd : Y.ok d = true)
    (h : VG.Proof.MlDsa.X86.Sign.In c d) : Region.Sub (c.rgn s₀) (d.rgn s₀) := by
  obtain ⟨e, h₁, h₂⟩ := h
  show Region.Sub ⟨c.addr s₀, c.len⟩ ⟨d.addr s₀, d.len⟩
  have ea : c.addr s₀ = (d.ptr s₀).setWidth 64 + BitVec.ofNat 64 (c.off - d.off) := by
    show c.addr s₀ = d.addr s₀ + _
    rw [Buf.addr_eq hp hc, Buf.addr_eq hp hd, BitVec.add_assoc, ← BitVec.ofNat_add, e,
      show d.off + (c.off - d.off) = c.off by omega]
  rw [ea]
  exact sub_of_contains (contains_at (by omega) (Buf.fit hp hd))

/-- The frame of a piece, widened to the buffers `ds`. -/
theorem frIn {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) {bs ds : List Buf} {N M : Nat} (hNM : N ≤ M) (hM : M ≤ 80)
    (h : ∀ c ∈ bs, (VG.Proof.MlDsa.X86.Sign.Y p).ok c = true ∧ ∃ d ∈ ds, (VG.Proof.MlDsa.X86.Sign.Y p).ok d = true ∧ VG.Proof.MlDsa.X86.Sign.In c d) {m m' : Mem}
    (fr : Frame (FR s₀ bs N) m m') : Frame (FR s₀ ds M) m m' :=
  fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hc', d, hd, hd', i⟩ := h c hc
      exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hd), VG.Proof.MlDsa.X86.Sign.rgn_sub hp hc' hd' i⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        stk_sub hp hNM (by show M + 16 ≤ 96; omega)⟩

theorem Frame.trans' {rs : List Region} {m₁ m₂ m₃ : Mem} (h₁ : Frame rs m₁ m₂) (h₂ : Frame rs m₂ m₃) :
    Frame rs m₁ m₃ := h₁.trans h₂

/-! ## Families of slots -/

/-- The `n` slots from `b` hold `f 0, …, f (n - 1)`. -/
def Fam (s₀ : State) (m : Mem) (b n : Nat) (f : Nat → VG.Spec.MlDsa.Poly) : Prop :=
  ∀ j < n, PolyIs m (Buf.addr s₀ (pS (b + j))) (f j)

theorem Fam.congr {s₀ : State} {m : Mem} {b n : Nat} {f g : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.X86.Sign.Fam s₀ m b n f)
    (e : ∀ j < n, f j = g j) : VG.Proof.MlDsa.X86.Sign.Fam s₀ m b n g := fun j hj => e j hj ▸ h j hj

/-- A buffer of `scratch` apart from `[lo, hi)`, or not in `scratch`. -/
def Out (p : Params) (lo hi : Nat) (c : Buf) : Prop :=
  (VG.Proof.MlDsa.X86.Sign.Y p).ok c = true ∧ (c.arg = SC → c.off + c.len ≤ lo ∨ hi ≤ c.off)

/-- The slots of `y`, `ŷ` and `w`. -/
abbrev yB (p : Params) : Nat := 5 + p.k
abbrev yhB (p : Params) : Nat := 5 + p.k + p.ℓ
abbrev wB (p : Params) : Nat := 5 + p.k + 2 * p.ℓ

/-- The slots of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
abbrev s1B (p : Params) : Nat := 5 + 2 * p.k + 2 * p.ℓ
abbrev s2B (p : Params) : Nat := 5 + 2 * p.k + 3 * p.ℓ
abbrev t0B (p : Params) : Nat := 5 + 3 * p.k + 3 * p.ℓ

/-- A write apart from all of the families. -/
def OutK (p : Params) (n1 n2 n0 : Nat) (c : Buf) : Prop :=
  VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.aBase p)) (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.nS p)) c ∧ VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.s1B p)) (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.s1B p + n1)) c ∧
    VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.s2B p)) (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.s2B p + n2)) c ∧ VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.t0B p)) (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.t0B p + n0)) c

/-- A write that an iteration of the loop may do: apart from `Â`, `ŝ₁`,
`ŝ₂`, `t̂₀`, `CNT`, `KAP` and `ρ″`. -/
def OutI (p : Params) (c : Buf) : Prop :=
  VG.Proof.MlDsa.X86.Sign.OutK p p.ℓ p.k p.k c ∧ VG.Proof.MlDsa.X86.Sign.Out p oCNT (oKAP + 4) c ∧ VG.Proof.MlDsa.X86.Sign.Out p oMS (oMS + 64) c

/-- A write that the checks of an iteration may do, with `nh` polynomials of
the hint made: apart from what `OutI` keeps, `ĉ`, `c̃`, `y`, `w`, the hint,
`OK` and `ONES`. -/
def OutC (p : Params) (nh : Nat) (c : Buf) : Prop :=
  VG.Proof.MlDsa.X86.Sign.OutI p c ∧ VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP 0) (VG.Impl.MlDsa.X86.Sign.oP 1) c ∧ VG.Proof.MlDsa.X86.Sign.Out p oCT (oCT + 64) c ∧ VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.yB p)) (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + p.k)) c ∧
    VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP 5) (VG.Impl.MlDsa.X86.Sign.oP (5 + nh)) c ∧ VG.Proof.MlDsa.X86.Sign.Out p oOK (oOK + 4) c ∧ VG.Proof.MlDsa.X86.Sign.Out p oONES (oONES + 4) c

theorem PS.w1pos {p : Params} (ps : VG.Proof.MlDsa.X86.Sign.PS p) : 0 < p.k * w1Len p :=
  Nat.mul_pos (by have := ps.hk; omega) (by rcases ps.hw1Len with h | h <;> omega)

/-- The facts of `PS p` that the offsets need, in the context. -/
macro "ofs" : tactic => do
  let ps := Lean.mkIdent `ps
  `(tactic| (
  have _ := ($ps).hk; have _ := ($ps).hl; have _ := ($ps).hscr; have _ := ($ps).hsigLen; have _ := ($ps).hskLen
  have _ := ($ps).hcLen; have _ := ($ps).hzLen; have _ := ($ps).hw1; have _ := ($ps).hω; have _ := PS.w1pos $ps
  try simp only [nS, aBase, s1B, s2B, t0B, yB, yhB, wB] at *
  set_option linter.unusedSimpArgs false in
  simp only [Lay.apart, Lay.okW_iff, Lay.ok_iff, Lay.sep_iff, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
    true_and, ne_eq, not_true_eq_false, false_and, or_false, true_or, or_true, Out, In,
    Y_n, Y_alen0, Y_alen1, Y_alen2, Y_alen3, Y_alen4, Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4,
    oP, SC, oPS, oRS, oHIN, oMS, oCT, oW1, oST, oWK, oOK, oCNT, oKAP, oONES, skS1, skS2, skT0, sigZ, sigH, aBase, s1B, s2B, t0B, OutK, OutI, OutC, yB, yhB, wB, bMu, bRnd, bSk, bSig]
  omega))

/-! ## Slots -/

section
variable (ps : VG.Proof.MlDsa.X86.Sign.PS p)
include ps

theorem slot_ok {j : Nat} (hj : j < VG.Proof.MlDsa.X86.Sign.nS p) : (VG.Proof.MlDsa.X86.Sign.Y p).okW (pS j) = true := by ofs
theorem slot_ok' {j : Nat} (hj : j < VG.Proof.MlDsa.X86.Sign.nS p) : (VG.Proof.MlDsa.X86.Sign.Y p).ok (pS j) = true := (Lay.okW_iff.mp (VG.Proof.MlDsa.X86.Sign.slot_ok ps hj)).1

omit ps in
theorem slot_sep {i j : Nat} (h : i ≠ j) : (VG.Proof.MlDsa.X86.Sign.Y p).sep (pS i) (pS j) = true := by
  simp only [Lay.sep_iff, VG.Impl.MlDsa.X86.Sign.oP, true_and, ne_eq, not_true_eq_false, false_and, or_false]; omega

omit ps in
/-- An entry of `Â` is a slot. -/
theorem aP_eq {i j : Nat} : VG.Impl.MlDsa.X86.Sign.aP p i j = pS (5 + 4 * p.k + 3 * p.ℓ + (p.ℓ * i + j)) := by
  simp only [VG.Impl.MlDsa.X86.Sign.aP, Nat.add_assoc]

omit ps in
theorem aIdx {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have : p.ℓ * i + p.ℓ ≤ p.ℓ * p.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [Nat.mul_comm p.k]; omega

end

theorem apart_of {b : Buf} (hb : (VG.Proof.MlDsa.X86.Sign.Y p).ok b = true) (hbs : b.arg = SC) {bs : List Buf}
    (h : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.Out p b.off (b.off + b.len) c) : (VG.Proof.MlDsa.X86.Sign.Y p).apart b bs = true := by
  simp only [Lay.apart, hb, Bool.true_and, List.all_eq_true, Bool.and_eq_true]
  intro c hc
  obtain ⟨hc₁, hc₂⟩ := h c hc
  refine ⟨hc₁, Lay.sep_iff.mpr ?_⟩
  by_cases e : b.arg = c.arg
  · exact .inl ⟨e, (hc₂ (e ▸ hbs)).symm⟩
  · exact .inr ⟨e, .inl (by rw [hbs]; rfl)⟩

theorem Fam.keep {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {b n : Nat} (hb : b + n ≤ VG.Proof.MlDsa.X86.Sign.nS p)
    (h : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP b) (VG.Impl.MlDsa.X86.Sign.oP (b + n)) c) {f : Nat → VG.Spec.MlDsa.Poly} (hf : VG.Proof.MlDsa.X86.Sign.Fam s₀ m b n f) : VG.Proof.MlDsa.X86.Sign.Fam s₀ m' b n f :=
  fun j hj => VG.Proof.MlDsa.Sign.polyIs_congr (VG.Proof.MlKem.X86.Top.keep hp (N := N) (by show N + 16 ≤ 96; omega)
    (VG.Proof.MlDsa.X86.Sign.apart_of (VG.Proof.MlDsa.X86.Sign.slot_ok' ps (Nat.lt_of_lt_of_le (by omega : b + j < b + n) hb)) rfl fun c hc => by
      obtain ⟨h₁, h₂⟩ := h c hc
      exact ⟨h₁, fun e => by simp only [VG.Impl.MlDsa.X86.Sign.oP] at h₂ ⊢; have := h₂ e; omega⟩) fr) (hf j hj)

theorem keepB {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {o l : Nat} (hc : (VG.Proof.MlDsa.X86.Sign.Y p).ok (sc o l) = true)
    (h : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.Out p o (o + l) c) : bytesAt m' (Buf.addr s₀ (sc o l)) l = bytesAt m (Buf.addr s₀ (sc o l)) l :=
  keepBytes hp (N := N) (by show N + 16 ≤ 96; omega) (VG.Proof.MlDsa.X86.Sign.apart_of hc rfl h) fr

theorem keepW' {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {o : Nat} (hc : (VG.Proof.MlDsa.X86.Sign.Y p).ok (sc o 4) = true)
    (h : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.Out p o (o + 4) c) : m'.readW (Buf.addr s₀ (sc o 4)) 32 = m.readW (Buf.addr s₀ (sc o 4)) 32 :=
  keepW hp (N := N) (by show N + 16 ≤ 96; omega) (VG.Proof.MlDsa.X86.Sign.apart_of hc rfl h) fr

theorem keepP {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {j : Nat} (hj : j < VG.Proof.MlDsa.X86.Sign.nS p)
    (h : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP j) (VG.Impl.MlDsa.X86.Sign.oP (j + 1)) c) {f : VG.Spec.MlDsa.Poly} (hf : PolyIs m (Buf.addr s₀ (pS j)) f) :
    PolyIs m' (Buf.addr s₀ (pS j)) f := by
  have := Fam.keep hp ps hN fr (b := j) (n := 1) (by omega) h (f := fun _ => f) fun i hi => by
    rw [show i = 0 by omega]; exact hf
  exact this 0 (by decide)

/-- The first `r` slots of a family, and the rest. -/
theorem Fam.snoc {s₀ : State} {m : Mem} {b n : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.X86.Sign.Fam s₀ m b n f)
    (h' : PolyIs m (Buf.addr s₀ (pS (b + n))) (f n)) : VG.Proof.MlDsa.X86.Sign.Fam s₀ m b (n + 1) f := fun j hj => by
  by_cases e : j < n
  · exact h j e
  · rw [show j = n by omega]; exact h'

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Words`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): words and bytes of `scratch`

The small blocks between calls, as what they leave in `scratch` and the frame
of what they change: a word or a byte set (`wp_st32`, `wp_st8`), `OK ← OK ∧
eax` (`wp_andOK`) and `ONES ← ONES + eax` (`wp_addOnes`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

theorem sc_ok (ps : VG.Proof.MlDsa.X86.Sign.PS p) {o n : Nat} (h : o + n ≤ 5120) (hn : 0 < n) : (VG.Proof.MlDsa.X86.Sign.Y p).okW (sc o n) = true := by ofs

theorem sc_ok' (ps : VG.Proof.MlDsa.X86.Sign.PS p) {o n : Nat} (h : o + n ≤ 5120) (hn : 0 < n) : (VG.Proof.MlDsa.X86.Sign.Y p).ok (sc o n) = true :=
  (Lay.okW_iff.mp (VG.Proof.MlDsa.X86.Sign.sc_ok ps h hn)).1

/-- The address of a part of a buffer. -/
theorem addr_off {Y : VG.Proof.MlKem.X86.Top.Lay} {s₀ : State} (hp : TPre Y s₀) {a o d l l' : Nat} (h₁ : Y.ok ⟨a, o, l⟩ = true)
    (h₂ : Y.ok ⟨a, o + d, l'⟩ = true) : Buf.addr s₀ ⟨a, o + d, l'⟩ = Buf.addr s₀ ⟨a, o, l⟩ + BitVec.ofNat 64 d := by
  rw [Buf.addr_eq hp h₂, Buf.addr_eq hp h₁, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bytes1_write (m : Mem) (a : Addr) (v : Byte) : bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
    VG.Proof.MlKem.writeW8_apply, ite_true]

theorem setWidth8_ofNat (v : Nat) : (BitVec.ofNat 32 v).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd v (by decide)

theorem and01 (a b : Bool) :
    ((if a then 1 else 0 : BitVec 32) &&& (if b then 1 else 0)) = if a && b then 1 else 0 := by
  cases a <;> cases b <;> rfl

section
variable {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
include hp h

/-- The word at `o` set to `v`. -/
theorem wp_st32 {o : Nat} (hc : (VG.Proof.MlDsa.X86.Sign.Y p).okW (sc o 4) = true) (v : Nat) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [sc o 4] 0) s.mem s'.mem → VG.Proof.MlDsa.X86.Sign.scw s₀ s' o = BitVec.ofNat 32 v →
      WP isa (.block is) s' Q) :
    WP isa (.block (st32 o v ++ is)) s Q := by
  simp only [st32, List.cons_append, List.nil_append]
  refine VG.Proof.MlKem.X86.Top.wp_movi fun s₁ o₁ v₁ => ?_
  refine VG.Proof.MlDsa.X86.Sign.wp_stsc hp (h.only o₁ (by simp) (by simp)) hc fun s₂ c₂ g₂ m₂ => k s₂ c₂ ?_ ?_
  · rw [m₂, o₁.mem]; exact frW32 (Y := VG.Proof.MlDsa.X86.Sign.Y p)
  · rw [VG.Proof.MlDsa.X86.Sign.scw, m₂, Mem.readW_writeW_self32, v₁]

/-- The byte at `o` set to `v`. -/
theorem wp_st8 {o : Nat} (hc : (VG.Proof.MlDsa.X86.Sign.Y p).okW (sc o 1) = true) (v : Nat) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [sc o 1] 0) s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ (sc o 1)) 1 = [BitVec.ofNat 8 v] → WP isa (.block is) s' Q) :
    WP isa (.block (st8 o v ++ is)) s Q := by
  simp only [st8, List.cons_append, List.nil_append]
  refine VG.Proof.MlKem.X86.Top.wp_movi fun s₁ o₁ v₁ => ?_
  refine VG.Proof.MlDsa.X86.Sign.wp_st8sc hp (h.only o₁ (by simp) (by simp)) hc fun s₂ c₂ g₂ m₂ => k s₂ c₂ ?_ ?_
  · rw [m₂, o₁.mem]; exact frW8 (Y := VG.Proof.MlDsa.X86.Sign.Y p)
  · rw [m₂, VG.Proof.MlDsa.X86.Sign.bytes1_write]; show [(s₁.gpr .eax).setWidth 8] = _; rw [v₁, VG.Proof.MlDsa.X86.Sign.setWidth8_ofNat]

/-- `OK ← OK ∧ eax`. -/
theorem wp_andOK (ps : VG.Proof.MlDsa.X86.Sign.PS p) {Q : State → Prop}
    (k : ∀ s', VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [sc oOK 4] 0) s.mem s'.mem →
      VG.Proof.MlDsa.X86.Sign.scw s₀ s' oOK = VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK &&& s.gpr .eax → Q s') :
    WP isa (.block andOK) s Q := by
  unfold andOK
  refine VG.Proof.MlDsa.X86.Sign.wp_ldsc hp h (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_andr fun s₂ o₂ v₂ => ?_
  have o := o₁.trans o₂
  refine VG.Proof.MlDsa.X86.Sign.wp_stsc hp (h.only o (by simp) (by simp)) (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) fun s₃ c₃ g₃ m₃ =>
    WP.block_nil_iff.mpr (k s₃ c₃ ?_ ?_)
  · rw [m₃, o.mem]; exact frW32 (Y := VG.Proof.MlDsa.X86.Sign.Y p)
  · rw [VG.Proof.MlDsa.X86.Sign.scw, m₃, Mem.readW_writeW_self32, v₂, v₁, o₁.gpr .eax (by simp)]

/-- `ONES ← ONES + eax`. -/
theorem wp_addOnes (ps : VG.Proof.MlDsa.X86.Sign.PS p) {Q : State → Prop}
    (k : ∀ s', VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [sc oONES 4] 0) s.mem s'.mem →
      VG.Proof.MlDsa.X86.Sign.scw s₀ s' oONES = VG.Proof.MlDsa.X86.Sign.scw s₀ s oONES + s.gpr .eax → Q s') :
    WP isa (.block VG.Impl.MlDsa.X86.Sign.addOnes) s Q := by
  unfold VG.Impl.MlDsa.X86.Sign.addOnes
  refine VG.Proof.MlDsa.X86.Sign.wp_ldsc hp h (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => VG.Proof.MlDsa.X86.Sign.wp_addr fun s₂ o₂ v₂ => ?_
  have o := o₁.trans o₂
  refine VG.Proof.MlDsa.X86.Sign.wp_stsc hp (h.only o (by simp) (by simp)) (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) fun s₃ c₃ g₃ m₃ =>
    WP.block_nil_iff.mpr (k s₃ c₃ ?_ ?_)
  · rw [m₃, o.mem]; exact frW32 (Y := VG.Proof.MlDsa.X86.Sign.Y p)
  · rw [VG.Proof.MlDsa.X86.Sign.scw, m₃, Mem.readW_writeW_self32, v₂, v₁, o₁.gpr .eax (by simp)]

end

/-! ## Frames of the small blocks -/

theorem fr0 {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80) {m m' : Mem}
    (fr : Frame (FR s₀ bs 0) m m') : Frame (FR s₀ bs N) m m' :=
  fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        stk_sub hp (Nat.zero_le N) (by show N + 16 ≤ 96; omega)⟩

theorem scr_ge (ps : VG.Proof.MlDsa.X86.Sign.PS p) : VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.nS p) ≤ VG.Proof.MlDsa.X86.Sign.scrLen p := by ofs

/-- The frame of a piece that writes only in `scratch[lo : hi]`, as that buffer. -/
theorem frSc {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) {bs : List Buf} {N M : Nat} (hNM : N ≤ M) (hM : M ≤ 80)
    {lo hi : Nat} (hlh : lo < hi) (hhi : hi ≤ VG.Proof.MlDsa.X86.Sign.scrLen p)
    (h : ∀ c ∈ bs, c.arg = SC ∧ lo ≤ c.off ∧ c.off + c.len ≤ hi ∧ 0 < c.len) {m m' : Mem}
    (fr : Frame (FR s₀ bs N) m m') : Frame (FR s₀ [sc lo (hi - lo)] M) m m' :=
  VG.Proof.MlDsa.X86.Sign.frIn hp hNM hM (fun c hc => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h c hc
    refine ⟨Lay.ok_iff.mpr ⟨by rw [h₁, VG.Proof.MlDsa.X86.Sign.Y_n]; decide, h₄, by rw [h₁, VG.Proof.MlDsa.X86.Sign.Y_alen4]; omega⟩, _, List.mem_singleton_self _,
      Lay.ok_iff.mpr ⟨by rw [VG.Proof.MlDsa.X86.Sign.Y_n]; exact (by decide : 4 < 5), by simp only; omega, by rw [VG.Proof.MlDsa.X86.Sign.Y_alen4]; simp only; omega⟩, h₁, by simp only; omega,
      by simp only; omega⟩) fr

/-- `keepB`, for bytes of `scratch` that may be none. -/
theorem keepB0 {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {o l : Nat} (L : Nat) (hl : o + l ≤ VG.Proof.MlDsa.X86.Sign.scrLen p)
    (h : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.Out p o (o + l) c) : bytesAt m' (Buf.addr s₀ (sc o L)) l = bytesAt m (Buf.addr s₀ (sc o L)) l := by
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rfl
  · exact VG.Proof.MlDsa.X86.Sign.keepB hp hN fr (l := l) (Lay.ok_iff.mpr ⟨by rw [VG.Proof.MlDsa.X86.Sign.Y_n]; exact (by decide : 4 < 5), hl0, by rw [VG.Proof.MlDsa.X86.Sign.Y_alen4]; exact hl⟩) h

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Prims`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the primitives it calls

What the proofs need of the implementations of the primitives (`PrimsOk`):
each is verified against its shared contract (`Spec/MlDsa/Poly.lean`), with 16
bytes of stack (56 for the samplers, which call the sponge functions), and
never writes `esp` (`COk`); and, of the two samplers whose result signing
branches on, that the result is a function of their public data (`rejF`,
`ballF`) that is 1 only when the algorithm finishes within `maxBounds`.

Each call (`…_piece`) is made from `Ctx`, with its buffers named as `Buf`s;
what it leaves unchanged is stated with the frame `FR s₀ bs 80` (its
buffers, and the stack below the function's own frame).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `k`, with the value returned in `eax` a function `F` of the entry state. -/
def withRet (k : Contract isa) (F : State → BitVec 32) : Contract isa :=
  { k with post := fun s s' => k.post s s' ∧ s'.gpr .eax = F s }

theorem verified_withRet {c : Prog isa} {k : Contract isa} {F : State → BitVec 32} (hv : Verified X86.target c k)
    (hr : ∀ s, k.pre s → ∀ t s', Exec isa c s t s' → s'.gpr .eax = F s) : Verified X86.target c (VG.Proof.MlDsa.X86.Sign.withRet k F) :=
  ⟨fun s hs => by
    obtain ⟨t, s', e, a, po⟩ := hv.1 s hs
    exact ⟨t, s', e, a, po, hr s hs t s' e⟩, hv.2.1, hv.2.2⟩

/-- What `vg_mldsa_rej_ntt_poly` returns, from its seed. -/
abbrev rejK (F : List Byte → Bool) : Contract isa :=
  VG.Proof.MlDsa.X86.Sign.withRet (rejNTTContract X86.abi 56) fun s => if F (bytesAt s.mem ((arg s 0).setWidth 64) 34) then 1 else 0

/-- What `vg_mldsa_sample_in_ball` returns, from `τ` and its seed. -/
abbrev ballK (F : Nat → List Byte → Bool) : Contract isa :=
  VG.Proof.MlDsa.X86.Sign.withRet (sampleInBallContract X86.abi 56) fun s =>
    if F (arg s 2).toNat (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) then 1 else 0

/-- What the proofs need of the implementations `P` of the primitives. -/
structure PrimsOk (P : Prims) where
  ntt : Verified X86.target P.ntt (nttContract X86.abi 16)
  invNtt : Verified X86.target P.invNtt (nttInvContract X86.abi 16)
  mul : Verified X86.target P.mul (mulContract X86.abi 16)
  mulAdd : Verified X86.target P.mulAdd (mulAddContract X86.abi 16)
  add : Verified X86.target P.add (addContract X86.abi 16)
  sub : Verified X86.target P.sub (subContract X86.abi 16)
  expandMask : Verified X86.target P.expandMask (expandMaskContract X86.abi 56)
  highBits : Verified X86.target P.highBits (highBitsContract X86.abi 16)
  lowBits : Verified X86.target P.lowBits (lowBitsContract X86.abi 16)
  normLt : Verified X86.target P.normLt (normLtContract X86.abi 16)
  makeHint : Verified X86.target P.makeHint (makeHintContract X86.abi 16)
  simpleBitPack : Verified X86.target P.simpleBitPack (simpleBitPackContract X86.abi 16)
  bitPack : Verified X86.target P.bitPack (bitPackContract X86.abi 16)
  bitUnpack : Verified X86.target P.bitUnpack (bitUnpackContract X86.abi 16)
  hintBitPack : Verified X86.target P.hintBitPack (hintBitPackContract X86.abi 16)
  /-- Whether `vg_mldsa_rej_ntt_poly` succeeds on a seed. -/
  rejF : List Byte → Bool
  rejNTT : Verified X86.target P.rejNTT (VG.Proof.MlDsa.X86.Sign.rejK rejF)
  rejMax : ∀ B, rejF B = true → (rejNTTPoly maxBounds.rejNTT B).isSome
  /-- Whether `vg_mldsa_sample_in_ball` succeeds on `τ` and a seed. -/
  ballF : Nat → List Byte → Bool
  ball : Verified X86.target P.ball (VG.Proof.MlDsa.X86.Sign.ballK ballF)
  ballMax : BallF ballF
  ok : ∀ c ∈ [P.ntt, P.invNtt, P.mul, P.mulAdd, P.add, P.sub, P.rejNTT, P.expandMask, P.ball, P.highBits,
    P.lowBits, P.normLt, P.makeHint, P.simpleBitPack, P.bitPack, P.bitUnpack, P.hintBitPack], VG.Proof.MlDsa.X86.Sign.COk c

/-- The returned `u32` is the low word, `eax`, of the returned pair. -/
theorem sw32 (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt b.isLt]
  omega

/-! ## Frames -/

/-- The frame of a call: its buffers, its arguments and its stack, within `FR s₀ bs 80`. -/
theorem fr80 {p : Params} {s₀ : State} {bs : List Buf} {N M : Nat} (hN : N ≤ 80) (hM : M ≤ 80) {m m' : Mem} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀)
    (fr : Frame ((bs.map (Buf.rgn s₀) ++ [below (E1 s₀) N]) ++ [below (E1 s₀) M]) m m') : Frame (FR s₀ bs 80) m m' :=
  fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp hN (by show 80 + 16 ≤ 96; omega)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp hM (by show 80 + 16 ≤ 96; omega)⟩

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimB`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): calls of the samplers

`RejNTTPoly` (`rej_piece`), a polynomial of `ExpandMask` (`mask_piece`) and
`SampleInBall` (`ball_piece`); the first and the last return whether they
succeeded, as a function of their seeds, which they may leak.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {A B : State → State → Prop}

/-- `a ← RejNTTPoly(seed)`, returning 1 or 0 in `eax`. -/
theorem rej_piece {F : List Byte → Bool} {nm : String} {c : Prog isa} (hv : Verified X86.target c (VG.Proof.MlDsa.X86.Sign.rejK F))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (da dO aa ao ca co : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨da, dO, 34⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨aa, ao, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨ca, co, 2048⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨da, dO, 34⟩ ⟨aa, ao, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨da, dO, 34⟩ ⟨ca, co, 2048⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀' → VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀' → A s₀ s → A s₀' s' →
      bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34 = bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 34⟩) 34)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩] 80) s.mem s'.mem →
      s'.gpr .eax = (if F (bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34) then 1 else 0) →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34)) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callPR nm c [.buf ⟨da, dO, 34⟩, .buf ⟨aa, ao, 1024⟩, .buf ⟨ca, co, 2048⟩]) := by
  set D : Buf := ⟨da, dO, 34⟩
  set R : Buf := ⟨aa, ao, 1024⟩
  set C : Buf := ⟨ca, co, 2048⟩
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hD, hR⟩, hC⟩, dDR⟩, dDC⟩, dRC⟩ := hc
  have hR' := (Lay.okW_iff.mp hR).1
  have hC' := (Lay.okW_iff.mp hC).1
  refine VG.Proof.MlDsa.X86.Sign.callPR_piece _ 3 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hD, hR', hC']) (fun s₀ => [D.rgn s₀])
    (fun s₀ => [R.rgn s₀, C.rgn s₀, below (E1 s₀) 12]) hA
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = D.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = C.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have eA : argAddr (pushed (argPush 3) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 3) (by decide)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 3) (by decide)
    obtain ⟨rD₁, rD₂, rD₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hD (n := 3) (K := 56) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hR' (n := 3) (K := 56) (by decide)
    obtain ⟨rC₁, rC₂, rC₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hC' (n := 3) (K := 56) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 3) (K := 56) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 3) (rd := [D.rgn s₀]) (wr := [R.rgn s₀, C.rgn s₀, below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hD h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inr (Buf.withinW hp hR' (Lay.okW_iff.mp hR).2 h.wr)
        · exact .inr (Buf.withinW hp hC' (Lay.okW_iff.mp hC).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eA eSp ⊢
    sig_pre [VG.Proof.MlDsa.X86.Sign.rejK, VG.Proof.MlDsa.X86.Sign.withRet, rejNTTContract, rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    exact ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hD hR' dDR, Buf.disj hp hD hC' dDC, rD₁, Buf.disj hp hR' hC' dRC, rR₁, rC₁,
      rD₂, rR₂, rC₂, rA₂, rD₃, rR₃, rC₃, rA₃, Buf.fit hp hD, Buf.fit hp hR', Buf.fit hp hC'⟩
  · have e₁ : D.ptr s₀ = D.ptr s₀' := hq.t.ptr hD
    have e₂ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR'
    have e₃ : C.ptr s₀ = C.ptr s₀' := hq.t.ptr hC'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, e₃, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = D.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = C.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a0' : arg (pushed (argPush 3) s₁').callEntry 0 = D.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .buf R, .buf C]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 3) s₁').callEntry 1 = R.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .buf R, .buf C]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 3) s₁').callEntry 2 = C.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .buf R, .buf C]) (by simp) hg' (i := 2) (by simp)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 3) (by decide)
    have eSp' : (pushed (argPush 3) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 3) (by decide)
    have b₁ := VG.Proof.MlKem.bytesAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hD)
    have b₂ := VG.Proof.MlKem.bytesAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp' h' (n := 3) (by decide) hD)
    have key : bytesAt (pushed (argPush 3) s₁).callEntry.mem (D.addr s₀) 34 =
        bytesAt (pushed (argPush 3) s₁').callEntry.mem (D.addr s₀') 34 := by
      rw [b₁, b₂, m, m']; exact hseed s₀ s₀' s s' hp hp' hq ha ha'
    simp only [Buf.addr, e₁] at key
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eSp key ⊢
    generalize he' : (pushed (argPush 3) s₁').callEntry = e' at a0' a1' a2' eSp' key ⊢
    sig_pub [VG.Proof.MlDsa.X86.Sign.rejK, VG.Proof.MlDsa.X86.Sign.withRet, rejNTTContract, rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a0', a1', a2', eSp, eSp', e₁, e₂, e₃, hq.t.E1, and_self, key]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Buf.inW hp hR' (Lay.okW_iff.mp hR).2
    · exact Buf.inW hp hC' (Lay.okW_iff.mp hC).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, g₂, post⟩ := post
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = D.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have b₁ : bytesAt (pushed (argPush 3) s₁).callEntry.mem ((D.ptr s₀).setWidth 64) 34 = bytesAt s.mem (D.addr s₀) 34 := by
      rw [← m]; exact VG.Proof.MlKem.bytesAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hD)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 post
    sig_post [VG.Proof.MlDsa.X86.Sign.rejK, VG.Proof.MlDsa.X86.Sign.withRet, rejNTTContract, rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂, VG.Proof.MlDsa.X86.Sign.sw32, g₂] at post
    rw [b₁] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post.2.2 post.1 post.2.1

/-- `a ←` a polynomial of `ExpandMask`, from the 66 bytes `seed`. -/
theorem mask_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (expandMaskContract X86.abi 56))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (g1 : Nat) (hg1 : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19) (da dO aa ao ca co : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨da, dO, 66⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨aa, ao, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨ca, co, 2048⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨da, dO, 66⟩ ⟨aa, ao, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨da, dO, 66⟩ ⟨ca, co, 2048⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)
        (toRq (VG.Spec.MlDsa.bitUnpack (VG.Spec.MlDsa.H (bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 66⟩) 66) (32 * (1 + bitlen (g1 - 1)))) (g1 - 1) g1)) →
      B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP nm c [.buf ⟨da, dO, 66⟩, .imm g1, .buf ⟨aa, ao, 1024⟩, .buf ⟨ca, co, 2048⟩]) := by
  set D : Buf := ⟨da, dO, 66⟩
  set R : Buf := ⟨aa, ao, 1024⟩
  set C : Buf := ⟨ca, co, 2048⟩
  have g1l : (BitVec.ofNat 32 g1).toNat = g1 := by rcases hg1 with rfl | rfl <;> rfl
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hD, hR⟩, hC⟩, dDR⟩, dDC⟩, dRC⟩ := hc
  have hR' := (Lay.okW_iff.mp hR).1
  have hC' := (Lay.okW_iff.mp hC).1
  refine VG.Proof.MlDsa.X86.Sign.callP_piece _ 4 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hD, hR', hC']) (fun s₀ => [D.rgn s₀])
    (fun s₀ => [R.rgn s₀, C.rgn s₀, below (E1 s₀) 16]) hA
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = D.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 g1 := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = C.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 3) (by simp)
    have eA : argAddr (pushed (argPush 4) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 4) (by decide)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 4) (by decide)
    obtain ⟨rD₁, rD₂, rD₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hD (n := 4) (K := 56) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hR' (n := 4) (K := 56) (by decide)
    obtain ⟨rC₁, rC₂, rC₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hC' (n := 4) (K := 56) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 4) (K := 56) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 4) (rd := [D.rgn s₀]) (wr := [R.rgn s₀, C.rgn s₀, below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hD h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inr (Buf.withinW hp hR' (Lay.okW_iff.mp hR).2 h.wr)
        · exact .inr (Buf.withinW hp hC' (Lay.okW_iff.mp hC).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eA eSp ⊢
    sig_pre [expandMaskContract, expandMaskSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, g1l]
    exact ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hD hR' dDR, Buf.disj hp hD hC' dDC, rD₁, Buf.disj hp hR' hC' dRC, rR₁, rC₁,
      rD₂, rR₂, rC₂, rA₂, rD₃, rR₃, rC₃, rA₃, Buf.fit hp hD, Buf.fit hp hR', Buf.fit hp hC', hg1⟩
  · have e₁ : D.ptr s₀ = D.ptr s₀' := hq.t.ptr hD
    have e₂ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR'
    have e₃ : C.ptr s₀ = C.ptr s₀' := hq.t.ptr hC'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, e₃, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = D.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 g1 := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = C.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 3) (by simp)
    have a0' : arg (pushed (argPush 4) s₁').callEntry 0 = D.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 4) s₁').callEntry 1 = BitVec.ofNat 32 g1 := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 4) s₁').callEntry 2 = R.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 4) s₁').callEntry 3 = C.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg' (i := 3) (by simp)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 4) (by decide)
    have eSp' : (pushed (argPush 4) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 4) (by decide)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eSp ⊢
    generalize he' : (pushed (argPush 4) s₁').callEntry = e' at a0' a1' a2' a3' eSp' ⊢
    sig_pub [expandMaskContract, expandMaskSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a0', a1', a2', a3', eSp, eSp', e₁, e₂, e₃, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Buf.inW hp hR' (Lay.okW_iff.mp hR).2
    · exact Buf.inW hp hC' (Lay.okW_iff.mp hC).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = D.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 g1 := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have b₁ : bytesAt (pushed (argPush 4) s₁).callEntry.mem ((D.ptr s₀).setWidth 64) 66 = bytesAt s.mem (D.addr s₀) 66 := by
      rw [← m]; exact VG.Proof.MlKem.bytesAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 4) (by decide) hD)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 post
    sig_post [expandMaskContract, expandMaskSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, m₂, g1l] at post
    rw [b₁] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `c ← SampleInBall(c̃)`, returning 1 or 0 in `eax`, with the `len` bytes `c̃`. -/
theorem ball_piece {F : Nat → List Byte → Bool} {nm : String} {c : Prog isa} (hv : Verified X86.target c (VG.Proof.MlDsa.X86.Sign.ballK F))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (len tau : Nat) (hlt : (len, tau) ∈ ballParams) (da dO aa ao ca co : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨da, dO, len⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨aa, ao, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨ca, co, 2048⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨da, dO, len⟩ ⟨aa, ao, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨da, dO, len⟩ ⟨ca, co, 2048⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀' → VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀' → A s₀ s → A s₀' s' →
      bytesAt s.mem (Buf.addr s₀ ⟨da, dO, len⟩) len = bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, len⟩) len)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩] 80) s.mem s'.mem →
      s'.gpr .eax = (if F tau (bytesAt s.mem (Buf.addr s₀ ⟨da, dO, len⟩) len) then 1 else 0) →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Outcome (fun b => (VG.Spec.MlDsa.sampleInBall tau b.ball (bytesAt s.mem (Buf.addr s₀ ⟨da, dO, len⟩) len)).map toRq)
        (s'.gpr .eax) (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callPR nm c [.buf ⟨da, dO, len⟩, .imm len, .imm tau, .buf ⟨aa, ao, 1024⟩, .buf ⟨ca, co, 2048⟩]) := by
  set D : Buf := ⟨da, dO, len⟩
  set R : Buf := ⟨aa, ao, 1024⟩
  set C : Buf := ⟨ca, co, 2048⟩
  have ll : (BitVec.ofNat 32 len).toNat = len := by simp [ballParams] at hlt; rcases hlt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have tl : (BitVec.ofNat 32 tau).toNat = tau := by simp [ballParams] at hlt; rcases hlt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hD, hR⟩, hC⟩, dDR⟩, dDC⟩, dRC⟩ := hc
  have hR' := (Lay.okW_iff.mp hR).1
  have hC' := (Lay.okW_iff.mp hC).1
  refine VG.Proof.MlDsa.X86.Sign.callPR_piece _ 5 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hD, hR', hC']) (fun s₀ => [D.rgn s₀])
    (fun s₀ => [R.rgn s₀, C.rgn s₀, below (E1 s₀) 20]) hA
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = D.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 tau := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = C.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 4) (by simp)
    have eA : argAddr (pushed (argPush 5) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 5) (by decide)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 5) (by decide)
    obtain ⟨rD₁, rD₂, rD₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hD (n := 5) (K := 56) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hR' (n := 5) (K := 56) (by decide)
    obtain ⟨rC₁, rC₂, rC₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hC' (n := 5) (K := 56) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 5) (K := 56) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 5) (rd := [D.rgn s₀]) (wr := [R.rgn s₀, C.rgn s₀, below (E1 s₀) 20])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hD h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inr (Buf.withinW hp hR' (Lay.okW_iff.mp hR).2 h.wr)
        · exact .inr (Buf.withinW hp hC' (Lay.okW_iff.mp hC).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eA eSp ⊢
    sig_pre [VG.Proof.MlDsa.X86.Sign.ballK, VG.Proof.MlDsa.X86.Sign.withRet, sampleInBallContract, sampleInBallSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, ll, tl]
    exact ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hD hR' dDR, Buf.disj hp hD hC' dDC, rD₁, Buf.disj hp hR' hC' dRC, rR₁, rC₁,
      rD₂, rR₂, rC₂, rA₂, rD₃, rR₃, rC₃, rA₃, Buf.fit hp hD, Buf.fit hp hR', Buf.fit hp hC', hlt⟩
  · have e₁ : D.ptr s₀ = D.ptr s₀' := hq.t.ptr hD
    have e₂ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR'
    have e₃ : C.ptr s₀ = C.ptr s₀' := hq.t.ptr hC'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, e₃, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = D.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 tau := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = C.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 4) (by simp)
    have a0' : arg (pushed (argPush 5) s₁').callEntry 0 = D.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 5) s₁').callEntry 1 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 5) s₁').callEntry 2 = BitVec.ofNat 32 tau := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 5) s₁').callEntry 3 = R.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg' (i := 3) (by simp)
    have a4' : arg (pushed (argPush 5) s₁').callEntry 4 = C.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg' (i := 4) (by simp)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 5) (by decide)
    have eSp' : (pushed (argPush 5) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 5) (by decide)
    have b₁ := VG.Proof.MlKem.bytesAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 5) (by decide) hD)
    have b₂ := VG.Proof.MlKem.bytesAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp' h' (n := 5) (by decide) hD)
    have key : bytesAt (pushed (argPush 5) s₁).callEntry.mem (D.addr s₀) len =
        bytesAt (pushed (argPush 5) s₁').callEntry.mem (D.addr s₀') len := by
      rw [b₁, b₂, m, m']; exact hseed s₀ s₀' s s' hp hp' hq ha ha'
    simp only [Buf.addr, e₁] at key
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eSp key ⊢
    generalize he' : (pushed (argPush 5) s₁').callEntry = e' at a0' a1' a2' a3' a4' eSp' key ⊢
    sig_pub [VG.Proof.MlDsa.X86.Sign.ballK, VG.Proof.MlDsa.X86.Sign.withRet, sampleInBallContract, sampleInBallSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a4, a0', a1', a2', a3', a4', eSp, eSp', e₁, e₂, e₃, hq.t.E1,
      and_self, ll, key]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Buf.inW hp hR' (Lay.okW_iff.mp hR).2
    · exact Buf.inW hp hC' (Lay.okW_iff.mp hC).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, g₂, post⟩ := post
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = D.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 tau := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 3) (by simp)
    have b₁ : bytesAt (pushed (argPush 5) s₁).callEntry.mem ((D.ptr s₀).setWidth 64) len = bytesAt s.mem (D.addr s₀) len := by
      rw [← m]; exact VG.Proof.MlKem.bytesAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 5) (by decide) hD)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 post
    sig_post [VG.Proof.MlDsa.X86.Sign.ballK, VG.Proof.MlDsa.X86.Sign.withRet, sampleInBallContract, sampleInBallSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, VG.Proof.MlDsa.X86.Sign.sw32, g₂, ll, tl] at post
    rw [b₁] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post.2.2 post.1 post.2.1

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseA`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): `ExpandA`

`ρ` is copied to `RS`, and entry `e` of `Â` (row `e / ℓ`, column `e % ℓ`) is
sampled into slot `aBase + e` from the seed `ρ ‖ e % ℓ ‖ e / ℓ` (`seedE`),
with `OK` the AND of the results (`okE`). After entry `e` (`IA e`): if every
entry so far succeeded, their slots hold them, within `maxBounds` (`aVal`);
otherwise one of them fails within `minBounds`.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

section
variable (p : Params)

/-- `ρ`, from the initial state. -/
abbrev rhoS (s₀ : State) : List Byte := rhoV (VG.Proof.MlDsa.X86.Sign.skOf p s₀)

/-- The seed of entry `e`. -/
abbrev seedE (s₀ : State) (e : Nat) : List Byte := aSeed (VG.Proof.MlDsa.X86.Sign.rhoS p s₀) (e / p.ℓ) (e % p.ℓ)

/-- Entry `e`, within `maxBounds`. -/
abbrev aVal (s₀ : State) (e : Nat) : VG.Spec.MlDsa.Poly := Av (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (e / p.ℓ) (e % p.ℓ)

/-- The first `e` entries were sampled. -/
def okE (F : List Byte → Bool) (s₀ : State) (e : Nat) : Bool := (List.range e).all fun e' => F (VG.Proof.MlDsa.X86.Sign.seedE p s₀ e')

end

theorem okE_succ {F : List Byte → Bool} {s₀ : State} {e : Nat} :
    VG.Proof.MlDsa.X86.Sign.okE p F s₀ (e + 1) = (VG.Proof.MlDsa.X86.Sign.okE p F s₀ e && F (VG.Proof.MlDsa.X86.Sign.seedE p s₀ e)) := by
  simp only [VG.Proof.MlDsa.X86.Sign.okE, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem okE_lt {F : List Byte → Bool} {s₀ : State} {e e' : Nat} (h : VG.Proof.MlDsa.X86.Sign.okE p F s₀ e = true) (he : e' < e) :
    F (VG.Proof.MlDsa.X86.Sign.seedE p s₀ e') = true :=
  List.all_eq_true.mp h e' (List.mem_range.mpr he)

/-- After entry `e`. -/
structure IA (p : Params) (F : List Byte → Bool) (e : Nat) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s
  rs : bytesAt s.mem (Buf.addr s₀ (sc oRS 32)) 32 = VG.Proof.MlDsa.X86.Sign.rhoS p s₀
  ok : VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = if VG.Proof.MlDsa.X86.Sign.okE p F s₀ e then 1 else 0
  fam : VG.Proof.MlDsa.X86.Sign.okE p F s₀ e = true → VG.Proof.MlDsa.X86.Sign.Fam s₀ s.mem (VG.Proof.MlDsa.X86.Sign.aBase p) e (VG.Proof.MlDsa.X86.Sign.aVal p s₀)
  bad : VG.Proof.MlDsa.X86.Sign.okE p F s₀ e = false → ∃ e' < e, rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.X86.Sign.seedE p s₀ e') = none

/-- The result of `vg_mldsa_rej_ntt_poly`, if it succeeded within `maxBounds`. -/
theorem rej_val {x : List Byte} {r : BitVec 32} {out : VG.Spec.MlDsa.Poly}
    (h : Outcome (fun b => rejNTTPoly b.rejNTT x) r out) (h1 : r = 1)
    (hm : (rejNTTPoly maxBounds.rejNTT x).isSome) : out = (rejNTTPoly maxBounds.rejNTT x).getD VG.Spec.MlDsa.zero := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    have e1 := VG.Proof.MlDsa.Sign.rejNTTPoly_mono (Nat.le_max_left b.rejNTT maxBounds.rejNTT) hb
    have e2 := VG.Proof.MlDsa.Sign.rejNTTPoly_mono (Nat.le_max_right b.rejNTT maxBounds.rejNTT) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem skLen_ge (ps : VG.Proof.MlDsa.X86.Sign.PS p) : 32 ≤ p.skLen := by have := ps.hskLen; omega

theorem rhoS_eq {s₀ s₀' : State} (ps : VG.Proof.MlDsa.X86.Sign.PS p) (hq : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') : VG.Proof.MlDsa.X86.Sign.rhoS p s₀ = VG.Proof.MlDsa.X86.Sign.rhoS p s₀' :=
  rho_of_leak (by rw [VG.Proof.MlKem.bytesAt_length]; exact VG.Proof.MlDsa.X86.Sign.skLen_ge ps)
    (by rw [VG.Proof.MlKem.bytesAt_length]; exact VG.Proof.MlDsa.X86.Sign.skLen_ge ps) hq.2

/-! ## An entry -/

/-- The bytes of the layout an entry needs. -/
theorem okRS (ps : VG.Proof.MlDsa.X86.Sign.PS p) : (VG.Proof.MlDsa.X86.Sign.Y p).ok (sc oRS 32) = true ∧ (VG.Proof.MlDsa.X86.Sign.Y p).okW (sc (oRS + 32) 1) = true ∧
    (VG.Proof.MlDsa.X86.Sign.Y p).okW (sc (oRS + 33) 1) = true ∧ (VG.Proof.MlDsa.X86.Sign.Y p).ok (sc oRS 33) = true ∧ (VG.Proof.MlDsa.X86.Sign.Y p).ok (sc oRS 34) = true ∧
    (VG.Proof.MlDsa.X86.Sign.Y p).ok (sc (oRS + 32) 1) = true ∧ (VG.Proof.MlDsa.X86.Sign.Y p).ok (sc (oRS + 33) 1) = true :=
  ⟨VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide), VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide), VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide),
    VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide), VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide), VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide),
    VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)⟩

theorem seed_bytes (ps : VG.Proof.MlDsa.X86.Sign.PS p) {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) {m : Mem} {ρ : List Byte} {i j : Nat}
    (hρ : bytesAt m (Buf.addr s₀ (sc oRS 32)) 32 = ρ)
    (hj : bytesAt m (Buf.addr s₀ (sc (oRS + 32) 1)) 1 = [BitVec.ofNat 8 j])
    (hi : bytesAt m (Buf.addr s₀ (sc (oRS + 33) 1)) 1 = [BitVec.ofNat 8 i]) :
    bytesAt m (Buf.addr s₀ (sc oRS 34)) 34 = aSeed ρ i j := by
  obtain ⟨o1, -, -, o4, o5, o6, o7⟩ := VG.Proof.MlDsa.X86.Sign.okRS ps
  rw [VG.Proof.MlDsa.X86.Sign.addr_off hp (d := 32) o5 o6] at hj
  rw [VG.Proof.MlDsa.X86.Sign.addr_off hp (d := 33) o5 o7] at hi
  rw [show Buf.addr s₀ (sc oRS 32) = Buf.addr s₀ (sc oRS 34) from rfl] at hρ
  rw [VG.Proof.MlKem.bytesAt_add _ _ 33 1, VG.Proof.MlKem.bytesAt_add _ _ 32 1, hρ, hj, hi, aSeed,
    VG.Proof.MlDsa.X86.Sign.integerToBytes_one, VG.Proof.MlDsa.X86.Sign.integerToBytes_one]

theorem rs_hi (ps : VG.Proof.MlDsa.X86.Sign.PS p) : oRS + 34 ≤ VG.Proof.MlDsa.X86.Sign.scrLen p := by
  have := VG.Proof.MlDsa.X86.Sign.scr_ge ps; simp only [VG.Impl.MlDsa.X86.Sign.oP, oRS, VG.Proof.MlDsa.X86.Sign.nS] at this ⊢; omega

/-- The two bytes of the seed of entry `e`. -/
theorem seedBlk_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.IA p F.rejF e) (fun s₀ s => VG.Proof.MlDsa.X86.Sign.IA p F.rejF e s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (sc oRS 34)) 34 = VG.Proof.MlDsa.X86.Sign.seedE p s₀ e)
      (.block (st8 (oRS + 32) (e % p.ℓ) ++ st8 (oRS + 33) (e / p.ℓ))) := by
  obtain ⟨o1, w2, w3, -, -, -, -⟩ := VG.Proof.MlDsa.X86.Sign.okRS ps
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.ctx) (fun s₀ s hp h => ?_) rfl
  refine VG.Proof.MlDsa.X86.Sign.wp_st8 hp h.ctx w2 _ fun s₁ c₁ f₁ b₁ => ?_
  rw [← List.append_nil (st8 (oRS + 33) (e / p.ℓ))]
  refine VG.Proof.MlDsa.X86.Sign.wp_st8 hp c₁ w3 _ fun s₂ c₂ f₂ b₂ => WP.block_nil_iff.mpr ?_
  have fs : ∀ o, o = oRS + 32 ∨ o = oRS + 33 → ∀ c ∈ [sc o 1], c.arg = SC ∧ oRS + 32 ≤ c.off ∧ c.off + c.len ≤ oRS + 34 ∧ 0 < c.len :=
    fun o ho c hc => by rw [List.mem_singleton] at hc; subst hc; simp only [oRS, true_and] at ho ⊢; omega
  have f := (VG.Proof.MlDsa.X86.Sign.frSc hp (M := 0) (Nat.le_refl _) (by decide) (by decide) (VG.Proof.MlDsa.X86.Sign.rs_hi ps) (fs _ (.inl rfl)) f₁).trans
    (VG.Proof.MlDsa.X86.Sign.frSc hp (M := 0) (Nat.le_refl _) (by decide) (by decide) (VG.Proof.MlDsa.X86.Sign.rs_hi ps) (fs _ (.inr rfl)) f₂)
  have o0 : ∀ c ∈ [sc (oRS + 32) (oRS + 34 - (oRS + 32))], VG.Proof.MlDsa.X86.Sign.Out p oOK (oOK + 4) c := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide), fun _ => by decide⟩
  have o1' : ∀ c ∈ [sc (oRS + 32) (oRS + 34 - (oRS + 32))], VG.Proof.MlDsa.X86.Sign.Out p oRS (oRS + 32) c := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide), fun _ => by decide⟩
  have oF : ∀ c ∈ [sc (oRS + 32) (oRS + 34 - (oRS + 32))], VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.aBase p)) (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.aBase p + e)) c := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc
    exact ⟨VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide), fun _ => .inl (by simp only [VG.Impl.MlDsa.X86.Sign.oP, oRS]; omega)⟩
  have hrs : bytesAt s₂.mem (Buf.addr s₀ (sc oRS 32)) 32 = VG.Proof.MlDsa.X86.Sign.rhoS p s₀ := by rw [VG.Proof.MlDsa.X86.Sign.keepB hp (by decide) f o1 o1', h.rs]
  refine ⟨⟨c₂, hrs, by rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) f (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) o0]; exact h.ok,
    fun hk => (h.fam hk).keep hp ps (by decide) f (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.aBase]; omega) oF, h.bad⟩, ?_⟩
  have b₁' : bytesAt s₂.mem (Buf.addr s₀ (sc (oRS + 32) 1)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := by
    rw [VG.Proof.MlDsa.X86.Sign.keepB hp (by decide) f₂ (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun c hc => by
      rw [List.mem_singleton] at hc; subst hc; exact ⟨VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide), fun _ => .inr (Nat.le_refl _)⟩, b₁]
  exact VG.Proof.MlDsa.X86.Sign.seed_bytes ps hp hrs b₁' b₂

/-- After the call of entry `e`. -/
structure RB (p : Params) (F : List Byte → Bool) (e : Nat) (s₀ s : State) : Prop where
  ia : VG.Proof.MlDsa.X86.Sign.IA p F e s₀ s
  eax : s.gpr .eax = if F (VG.Proof.MlDsa.X86.Sign.seedE p s₀ e) then 1 else 0
  yes : F (VG.Proof.MlDsa.X86.Sign.seedE p s₀ e) = true → PolyIs s.mem (Buf.addr s₀ (pS (VG.Proof.MlDsa.X86.Sign.aBase p + e))) (VG.Proof.MlDsa.X86.Sign.aVal p s₀ e)
  no : F (VG.Proof.MlDsa.X86.Sign.seedE p s₀ e) = false → rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.X86.Sign.seedE p s₀ e) = none

theorem rej_lay (ps : VG.Proof.MlDsa.X86.Sign.PS p) {e : Nat} (he : e < p.k * p.ℓ) :
    ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨SC, oRS, 34⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.aBase p + e), 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, oPS, 2048⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨SC, oRS, 34⟩ ⟨SC, VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.aBase p + e), 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨SC, oRS, 34⟩ ⟨SC, oPS, 2048⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨SC, VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.aBase p + e), 1024⟩ ⟨SC, oPS, 2048⟩) = true := by ofs

/-- The call of entry `e`. -/
theorem rejCall_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlDsa.X86.Sign.IA p F.rejF e s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sc oRS 34)) 34 = VG.Proof.MlDsa.X86.Sign.seedE p s₀ e)
      (VG.Proof.MlDsa.X86.Sign.RB p F.rejF e)
      (callPR "vg_mldsa_rej_ntt_poly" P.rejNTT [.buf (sc oRS 34), .buf (pS (VG.Proof.MlDsa.X86.Sign.aBase p + e)), .buf bPS]) := by
  refine VG.Proof.MlDsa.X86.Sign.rej_piece F.rejNTT (F.ok _ (by simp)) SC oRS SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.aBase p + e)) SC oPS (VG.Proof.MlDsa.X86.Sign.rej_lay ps he)
    (fun _ _ _ h => h.1.ctx) (fun s₀ s₀' s s' hp hp' hq h h' => by
      rw [h.2, h'.2]; show aSeed (VG.Proof.MlDsa.X86.Sign.rhoS p s₀) _ _ = aSeed (VG.Proof.MlDsa.X86.Sign.rhoS p s₀') _ _; rw [VG.Proof.MlDsa.X86.Sign.rhoS_eq ps hq])
    fun s₀ s s' hp ⟨h, hs⟩ c' fr heax hred hout => ?_
  rw [hs] at heax hout
  have hj : VG.Proof.MlDsa.X86.Sign.aBase p + e < VG.Proof.MlDsa.X86.Sign.nS p := by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.aBase]; omega
  refine ⟨⟨c', by rw [VG.Proof.MlDsa.X86.Sign.keepB hp (by decide) fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs), h.rs],
    by rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ok,
    fun hk => (h.fam hk).keep hp ps (by decide) fr (by omega) (by ofs), h.bad⟩, heax, fun hy => ?_, fun hn => ?_⟩
  · rw [hy] at heax; simp only [↓reduceIte] at heax
    refine ⟨hred heax, ?_⟩
    rw [VG.Proof.MlDsa.X86.Sign.rej_val hout heax (F.rejMax _ hy)]
    rfl
  · rw [hn] at heax
    rcases hout with ⟨h1, _⟩ | ⟨_, h0⟩
    · rw [heax] at h1; cases h1
    · exact h0

/-- `OK ← OK ∧ eax` after the call of entry `e`. -/
theorem rejAnd_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.RB p F.rejF e) (VG.Proof.MlDsa.X86.Sign.IA p F.rejF (e + 1)) (.block andOK) := by
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.ia.ctx) (fun s₀ s hp h => VG.Proof.MlDsa.X86.Sign.wp_andOK hp h.ia.ctx ps fun s' c' fr ok' => ?_) rfl
  have hj : VG.Proof.MlDsa.X86.Sign.aBase p + e < VG.Proof.MlDsa.X86.Sign.nS p := by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.aBase]; omega
  have fr' := VG.Proof.MlDsa.X86.Sign.fr0 hp (N := 80) (by decide) fr
  have hfam : VG.Proof.MlDsa.X86.Sign.okE p F.rejF s₀ e = true → VG.Proof.MlDsa.X86.Sign.Fam s₀ s'.mem (VG.Proof.MlDsa.X86.Sign.aBase p) e (VG.Proof.MlDsa.X86.Sign.aVal p s₀) := fun hk =>
    (h.ia.fam hk).keep hp ps (by decide) fr' (by omega) (by ofs)
  refine ⟨c', by rw [VG.Proof.MlDsa.X86.Sign.keepB hp (by decide) fr' (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs), h.ia.rs], ?_, fun hk => ?_, fun hk => ?_⟩
  · rw [ok', h.ia.ok, h.eax, VG.Proof.MlDsa.X86.Sign.and01, VG.Proof.MlDsa.X86.Sign.okE_succ]
  · rw [VG.Proof.MlDsa.X86.Sign.okE_succ, Bool.and_eq_true] at hk
    exact (hfam hk.1).snoc (VG.Proof.MlDsa.X86.Sign.keepP hp ps (by decide) fr' hj (by ofs) (h.yes hk.2))
  · rw [VG.Proof.MlDsa.X86.Sign.okE_succ, Bool.and_eq_false_iff] at hk
    rcases hk with hk | hk
    · obtain ⟨e', he', hn⟩ := h.ia.bad hk
      exact ⟨e', by omega, hn⟩
    · exact ⟨e, by omega, h.no hk⟩

theorem aP_slot {e : Nat} : VG.Impl.MlDsa.X86.Sign.aP p (e / p.ℓ) (e % p.ℓ) = pS (VG.Proof.MlDsa.X86.Sign.aBase p + e) := by
  rw [VG.Proof.MlDsa.X86.Sign.aP_eq, Nat.div_add_mod]

/-- Entry `e` of `Â`. -/
theorem sampleE_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.IA p F.rejF e) (VG.Proof.MlDsa.X86.Sign.IA p F.rejF (e + 1)) (sampleE P p e) := by
  unfold sampleE rejAt
  rw [VG.Proof.MlDsa.X86.Sign.aP_slot]
  exact (VG.Proof.MlDsa.X86.Sign.seedBlk_piece F ps e he).seq ((VG.Proof.MlDsa.X86.Sign.rejCall_piece F ps e he).seq (VG.Proof.MlDsa.X86.Sign.rejAnd_piece F ps e he))

/-- `ρ` to `RS`, and `Â`. -/
theorem expandA_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = 1) (VG.Proof.MlDsa.X86.Sign.IA p F.rejF (p.k * p.ℓ)) (Impl.MlDsa.X86.Sign.expandA P p) := by
  unfold Impl.MlDsa.X86.Sign.expandA
  refine Piece.seq (B := VG.Proof.MlDsa.X86.Sign.IA p F.rejF 0) (VG.Proof.MlDsa.X86.Sign.copy_piece 0 0 SC oRS 8 (by decide) (by decide) (by ofs)
    (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hb => ?_)
    (by simpa using VG.Proof.MlDsa.X86.Sign.seqR_piece (I := VG.Proof.MlDsa.X86.Sign.IA p F.rejF) 0 (p.k * p.ℓ) fun e _ he => VG.Proof.MlDsa.X86.Sign.sampleE_piece F ps e (by omega))
  have fr' : Frame (FR s₀ [sc oRS 32] 80) s.mem s'.mem := fr.mono (by simp)
  refine ⟨c', ?_, ?_, fun _ j hj => absurd hj (Nat.not_lt_zero _), fun hk => absurd hk (by simp [VG.Proof.MlDsa.X86.Sign.okE])⟩
  · show bytesAt s'.mem (Buf.addr s₀ ⟨SC, oRS, 4 * 8⟩) (4 * 8) = _
    rw [hb, h.1.roBytes hp (b := ⟨0, 0, 4 * 8⟩) (by ofs) rfl]
    exact (VG.Proof.MlKem.bytesAt_take _ _ (VG.Proof.MlDsa.X86.Sign.skLen_ge ps)).symm
  · rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) fr' (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)]
    simp [VG.Proof.MlDsa.X86.Sign.okE, h.2]

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimA`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): calls of the arithmetic primitives

`NTT` and `NTT⁻¹` in place (`inPlace_piece`), products (`mul_piece`, with or
without the sum), and sums and differences (`acc_piece`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {A B : State → State → Prop}

/-- `f ← t(f)`, with the working space `PS`. -/
theorem inPlace_piece {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (inPlaceContract X86.abi t 16)) (ok : VG.Proof.MlDsa.X86.Sign.COk c) (f : Buf) (hf : f.len = 1024)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).okW f && (VG.Proof.MlDsa.X86.Sign.Y p).okW (sc oPS 1024) && (VG.Proof.MlDsa.X86.Sign.Y p).sep f (sc oPS 1024)) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ Reduced s.mem (f.addr s₀))
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [f, sc oPS 1024] 80) s.mem s'.mem →
      PolyIs s'.mem (f.addr s₀) (t (polyAt s.mem (f.addr s₀))) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP nm c [.buf f, .buf (sc oPS 1024)]) := by
  obtain ⟨fa, fo, fl⟩ := f
  simp only at hf
  subst hf
  set f : Buf := ⟨fa, fo, 1024⟩ with hfd
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hS⟩, dFS⟩ := hc
  have hF' := (Lay.okW_iff.mp hF).1
  have hS' := (Lay.okW_iff.mp hS).1
  refine VG.Proof.MlDsa.X86.Sign.callP_piece _ 2 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hF', hS']) (fun _ => [])
    (fun s₀ => [f.rgn s₀, Buf.rgn s₀ (sc oPS 1024), below (E1 s₀) 8]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = f.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = Buf.ptr s₀ (sc oPS 1024) := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg (i := 1) (by simp)
    have eA : argAddr (pushed (argPush 2) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 2) (by decide)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 2) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hF' (n := 2) (K := 16) (by decide)
    obtain ⟨rS₁, rS₂, rS₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hS' (n := 2) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 2) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 2) (rd := []) (wr := [f.rgn s₀, Buf.rgn s₀ (sc oPS 1024), below (E1 s₀) 8])
      (fun r hr => absurd hr (by simp)) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inr (Buf.withinW hp hF' (Lay.okW_iff.mp hF).2 h.wr)
        · exact .inr (Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eA eSp ⊢
    sig_pre [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, Buf.disj hp hF' hS' dFS, rF₁, rS₁, rF₂, rS₂, rA₂, rF₃, rS₃, rA₃, Buf.fit hp hF', Buf.fit hp hS', ?_⟩
    exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 2) (by decide) hF') (m ▸ (hA s₀ s hp ha).2)
  · have e₁ : f.ptr s₀ = f.ptr s₀' := hq.t.ptr hF'
    have e₂ : Buf.ptr s₀ (sc oPS 1024) = Buf.ptr s₀' (sc oPS 1024) := hq.t.ptr hS'
    refine ⟨rfl, by simp only [Buf.rgn, e₁, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = f.ptr s₀ :=
      VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = Buf.ptr s₀ (sc oPS 1024) :=
      VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg (i := 1) (by simp)
    have a0' : arg (pushed (argPush 2) s₁').callEntry 0 = f.ptr s₀' :=
      VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 2) s₁').callEntry 1 = Buf.ptr s₀' (sc oPS 1024) :=
      VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg' (i := 1) (by simp)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 2) (by decide)
    have eSp' : (pushed (argPush 2) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 2) (by decide)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eSp ⊢
    generalize he' : (pushed (argPush 2) s₁').callEntry = e' at a0' a1' eSp' ⊢
    sig_pub [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a0', a1', eSp, eSp', e₁, e₂, hq.t.E1]
    exact ⟨trivial, trivial, trivial⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Buf.inW hp hF' (Lay.okW_iff.mp hF).2
    · exact Buf.inW hp hS' (Lay.okW_iff.mp hS).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = f.ptr s₀ :=
      VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg (i := 0) (by simp)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 post
    sig_post [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, m₂] at post
    rw [VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 2) (by decide) hF'), m] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

end VG.Proof.MlDsa.X86.Sign

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {A B : State → State → Prop}

/-- `h ← MultiplyNTT(f, g)`. -/
theorem mul_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (mulContract X86.abi 16))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (ha ho fa fo ga go : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨ha, ho, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨fa, fo, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨ga, go, 1024⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨ha, ho, 1024⟩ ⟨fa, fo, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨ha, ho, 1024⟩ ⟨ga, go, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧ Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [⟨ha, ho, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨ha, ho, 1024⟩)
        (multiplyNTT (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) →
      B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP nm c [.buf ⟨ha, ho, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  set H : Buf := ⟨ha, ho, 1024⟩
  set F : Buf := ⟨fa, fo, 1024⟩
  set G : Buf := ⟨ga, go, 1024⟩
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hH, hF⟩, hG⟩, dHF⟩, dHG⟩ := hc
  have hH' := (Lay.okW_iff.mp hH).1
  refine VG.Proof.MlDsa.X86.Sign.callP_piece _ 3 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hH', hF, hG]) (fun s₀ => [F.rgn s₀, G.rgn s₀])
    (fun s₀ => [H.rgn s₀, below (E1 s₀) 12]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    have eA : argAddr (pushed (argPush 3) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 3) (by decide)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 3) (by decide)
    obtain ⟨rH₁, rH₂, rH₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hH' (n := 3) (K := 16) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hF (n := 3) (K := 16) (by decide)
    obtain ⟨rG₁, rG₂, rG₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hG (n := 3) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 3) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 3) (rd := [F.rgn s₀, G.rgn s₀]) (wr := [H.rgn s₀, below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Buf.within hp hF h.rd h.wr
        · exact Buf.within hp hG h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hH' (Lay.okW_iff.mp hH).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eA eSp ⊢
    sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hH' hF dHF, Buf.disj hp hH' hG dHG, rH₁, rF₁, rG₁, rH₂, rF₂, rG₂, rA₂, rH₃, rF₃, rG₃, rA₃,
      Buf.fit hp hH', Buf.fit hp hF, Buf.fit hp hG, ?_, ?_⟩
    · exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hF) (m ▸ (hA s₀ s hp ha).2.1)
    · exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hG) (m ▸ (hA s₀ s hp ha).2.2)
  · have e₁ : H.ptr s₀ = H.ptr s₀' := hq.t.ptr hH'
    have e₂ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF
    have e₃ : G.ptr s₀ = G.ptr s₀' := hq.t.ptr hG
    refine ⟨by simp only [Buf.rgn, e₂, e₃], by simp only [Buf.rgn, e₁, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    have a0' : arg (pushed (argPush 3) s₁').callEntry 0 = H.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 3) s₁').callEntry 1 = F.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 3) s₁').callEntry 2 = G.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 2) (by simp)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 3) (by decide)
    have eSp' : (pushed (argPush 3) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 3) (by decide)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eSp ⊢
    generalize he' : (pushed (argPush 3) s₁').callEntry = e' at a0' a1' a2' eSp' ⊢
    sig_pub [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a0', a1', a2', eSp, eSp', e₁, e₂, e₃, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hH' (Lay.okW_iff.mp hH).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 post
    sig_post [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, m₂] at post
    rw [VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hF), VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hG),
      m] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `h ← h + MultiplyNTT(f, g)`. -/
theorem mulAdd_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (mulAddContract X86.abi 16))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (ha ho fa fo ga go : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨ha, ho, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨fa, fo, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨ga, go, 1024⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨ha, ho, 1024⟩ ⟨fa, fo, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨ha, ho, 1024⟩ ⟨ga, go, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ha, ho, 1024⟩) ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧ Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [⟨ha, ho, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨ha, ho, 1024⟩) (VG.Spec.MlDsa.add (polyAt s.mem (Buf.addr s₀ ⟨ha, ho, 1024⟩))
        (multiplyNTT (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩)))) →
      B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP nm c [.buf ⟨ha, ho, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  set H : Buf := ⟨ha, ho, 1024⟩
  set F : Buf := ⟨fa, fo, 1024⟩
  set G : Buf := ⟨ga, go, 1024⟩
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hH, hF⟩, hG⟩, dHF⟩, dHG⟩ := hc
  have hH' := (Lay.okW_iff.mp hH).1
  refine VG.Proof.MlDsa.X86.Sign.callP_piece _ 3 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hH', hF, hG]) (fun s₀ => [F.rgn s₀, G.rgn s₀])
    (fun s₀ => [H.rgn s₀, below (E1 s₀) 12]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    have eA : argAddr (pushed (argPush 3) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 3) (by decide)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 3) (by decide)
    obtain ⟨rH₁, rH₂, rH₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hH' (n := 3) (K := 16) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hF (n := 3) (K := 16) (by decide)
    obtain ⟨rG₁, rG₂, rG₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hG (n := 3) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 3) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 3) (rd := [F.rgn s₀, G.rgn s₀]) (wr := [H.rgn s₀, below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Buf.within hp hF h.rd h.wr
        · exact Buf.within hp hG h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hH' (Lay.okW_iff.mp hH).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eA eSp ⊢
    sig_pre [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hH' hF dHF, Buf.disj hp hH' hG dHG, rH₁, rF₁, rG₁, rH₂, rF₂, rG₂, rA₂, rH₃, rF₃, rG₃, rA₃,
      Buf.fit hp hH', Buf.fit hp hF, Buf.fit hp hG, ?_, ?_, ?_⟩
    · exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hH') (m ▸ (hA s₀ s hp ha).2.1)
    · exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hF) (m ▸ (hA s₀ s hp ha).2.2.1)
    · exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hG) (m ▸ (hA s₀ s hp ha).2.2.2)
  · have e₁ : H.ptr s₀ = H.ptr s₀' := hq.t.ptr hH'
    have e₂ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF
    have e₃ : G.ptr s₀ = G.ptr s₀' := hq.t.ptr hG
    refine ⟨by simp only [Buf.rgn, e₂, e₃], by simp only [Buf.rgn, e₁, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    have a0' : arg (pushed (argPush 3) s₁').callEntry 0 = H.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 3) s₁').callEntry 1 = F.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 3) s₁').callEntry 2 = G.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 2) (by simp)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 3) (by decide)
    have eSp' : (pushed (argPush 3) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 3) (by decide)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eSp ⊢
    generalize he' : (pushed (argPush 3) s₁').callEntry = e' at a0' a1' a2' eSp' ⊢
    sig_pub [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a0', a1', a2', eSp, eSp', e₁, e₂, e₃, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hH' (Lay.okW_iff.mp hH).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 post
    sig_post [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, m₂] at post
    rw [VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hH'), VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hF), VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hG),
      m] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `f ← op(f, g)` (`vg_mldsa_add`, `vg_mldsa_sub`). -/
theorem acc_piece {op : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (accSig.contract X86.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := 16)))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (fa fo ga go : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨fa, fo, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨ga, go, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (op (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP nm c [.buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  set F : Buf := ⟨fa, fo, 1024⟩
  set G : Buf := ⟨ga, go, 1024⟩
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hG⟩, dFG⟩ := hc
  have hF' := (Lay.okW_iff.mp hF).1
  refine VG.Proof.MlDsa.X86.Sign.callP_piece _ 2 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hF', hG]) (fun s₀ => [G.rgn s₀])
    (fun s₀ => [F.rgn s₀, below (E1 s₀) 8]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = G.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have eA : argAddr (pushed (argPush 2) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 2) (by decide)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 2) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hF' (n := 2) (K := 16) (by decide)
    obtain ⟨rG₁, rG₂, rG₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hG (n := 2) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 2) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 2) (rd := [G.rgn s₀]) (wr := [F.rgn s₀, below (E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hG h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hF' (Lay.okW_iff.mp hF).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eA eSp ⊢
    sig_pre [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hF' hG dFG, rF₁, rG₁, rF₂, rG₂, rA₂, rF₃, rG₃, rA₃,
      Buf.fit hp hF', Buf.fit hp hG, ?_, ?_⟩
    · exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 2) (by decide) hF') (m ▸ (hA s₀ s hp ha).2.1)
    · exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 2) (by decide) hG) (m ▸ (hA s₀ s hp ha).2.2)
  · have e₁ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF'
    have e₂ : G.ptr s₀ = G.ptr s₀' := hq.t.ptr hG
    refine ⟨by simp only [Buf.rgn, e₂], by simp only [Buf.rgn, e₁, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = G.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a0' : arg (pushed (argPush 2) s₁').callEntry 0 = F.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .buf G]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 2) s₁').callEntry 1 = G.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .buf G]) (by simp) hg' (i := 1) (by simp)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 2) (by decide)
    have eSp' : (pushed (argPush 2) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 2) (by decide)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eSp ⊢
    generalize he' : (pushed (argPush 2) s₁').callEntry = e' at a0' a1' eSp' ⊢
    sig_pub [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a0', a1', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hF' (Lay.okW_iff.mp hF).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = G.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 post
    sig_post [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂] at post
    rw [VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 2) (by decide) hF'), VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 2) (by decide) hG),
      m] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimD`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): calls of the encodings

`SimpleBitPack` (`sbp_piece`), `BitPack` (`bp_piece`), `BitUnpack`
(`bu_piece`) and `HintBitPack` (`hbp_piece`, which may leak the hint).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {A B : State → State → Prop}

/-- `out ← SimpleBitPack(f, b)`, `len` bytes. -/
theorem sbp_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (simpleBitPackContract X86.abi 16))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (b len : Nat) (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (fa fo oa oo : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨fa, fo, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨oa, oo, len⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨fa, fo, 1024⟩ ⟨oa, oo, len⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ ∀ i < n, (coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat ≤ b)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [⟨oa, oo, len⟩] 80) s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, len⟩) len = VG.Spec.MlDsa.simpleBitPack (natPolyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) b →
      B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP nm c [.buf ⟨fa, fo, 1024⟩, .imm b, .buf ⟨oa, oo, len⟩, .imm len]) := by
  set F : Buf := ⟨fa, fo, 1024⟩
  set O : Buf := ⟨oa, oo, len⟩
  have bl : (BitVec.ofNat 32 b).toNat = b := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> rfl
  have ll : (BitVec.ofNat 32 len).toNat = len := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> subst hl <;> rfl
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hO⟩, dFO⟩ := hc
  have hO' := (Lay.okW_iff.mp hO).1
  refine VG.Proof.MlDsa.X86.Sign.callP_piece _ 4 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hF, hO']) (fun s₀ => [F.rgn s₀])
    (fun s₀ => [O.rgn s₀, below (E1 s₀) 16]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    have eA : argAddr (pushed (argPush 4) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 4) (by decide)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 4) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hF (n := 4) (K := 16) (by decide)
    obtain ⟨rO₁, rO₂, rO₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hO' (n := 4) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 4) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 4) (rd := [F.rgn s₀]) (wr := [O.rgn s₀, below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hF h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eA eSp ⊢
    sig_pre [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, bl, ll]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hF hO' dFO, rF₁, rO₁, rF₂, rO₂, rA₂, rF₃, rO₃, rA₃,
      Buf.fit hp hF, Buf.fit hp hO', hb, hl, fun i hi => ?_⟩
    rw [coeffAt_congr₂ (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 4) (by decide) hF) hi, m]; exact (hA s₀ s hp ha).2 i hi
  · have e₁ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF
    have e₂ : O.ptr s₀ = O.ptr s₀' := hq.t.ptr hO'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    have a0' : arg (pushed (argPush 4) s₁').callEntry 0 = F.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 4) s₁').callEntry 1 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 4) s₁').callEntry 2 = O.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 4) s₁').callEntry 3 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg' (i := 3) (by simp)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 4) (by decide)
    have eSp' : (pushed (argPush 4) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 4) (by decide)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eSp ⊢
    generalize he' : (pushed (argPush 4) s₁').callEntry = e' at a0' a1' a2' a3' eSp' ⊢
    sig_pub [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a0', a1', a2', a3', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hO' (Lay.okW_iff.mp hO).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 post
    sig_post [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, bl, ll] at post
    rw [natPolyAt_congr₂ (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 4) (by decide) hF), m] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `out ← BitPack(f mod± q, a, b)`, `len` bytes. -/
theorem bp_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (bitPackContract X86.abi 16))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (a b len : Nat) (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b))
    (hs : a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ len < 2 ^ 32) (fa fo oa oo : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨fa, fo, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨oa, oo, len⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨fa, fo, 1024⟩ ⟨oa, oo, len⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      ∀ i < n, -(a : Int) ≤ modPm (coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat q ∧
        modPm (coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat q ≤ b)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [⟨oa, oo, len⟩] 80) s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, len⟩) len =
        VG.Spec.MlDsa.bitPack ((polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)).map fun c => modPm c.val q) a b → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP nm c [.buf ⟨fa, fo, 1024⟩, .imm a, .imm b, .buf ⟨oa, oo, len⟩, .imm len]) := by
  set F : Buf := ⟨fa, fo, 1024⟩
  set O : Buf := ⟨oa, oo, len⟩
  have al : (BitVec.ofNat 32 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  have bl : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  have ll : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hO⟩, dFO⟩ := hc
  have hO' := (Lay.okW_iff.mp hO).1
  refine VG.Proof.MlDsa.X86.Sign.callP_piece _ 5 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hF, hO']) (fun s₀ => [F.rgn s₀])
    (fun s₀ => [O.rgn s₀, below (E1 s₀) 20]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 a := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 4) (by simp)
    have eA : argAddr (pushed (argPush 5) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 5) (by decide)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 5) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hF (n := 5) (K := 16) (by decide)
    obtain ⟨rO₁, rO₂, rO₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hO' (n := 5) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 5) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 5) (rd := [F.rgn s₀]) (wr := [O.rgn s₀, below (E1 s₀) 20])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hF h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eA eSp ⊢
    sig_pre [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, al, bl, ll]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hF hO' dFO, rF₁, rO₁, rF₂, rO₂, rA₂, rF₃, rO₃, rA₃,
      Buf.fit hp hF, Buf.fit hp hO', hab, hl, ?_, fun i hi => ?_⟩
    · exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 5) (by decide) hF) (m ▸ (hA s₀ s hp ha).2.1)
    · rw [coeffAt_congr₂ (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 5) (by decide) hF) hi, m]; exact (hA s₀ s hp ha).2.2 i hi
  · have e₁ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF
    have e₂ : O.ptr s₀ = O.ptr s₀' := hq.t.ptr hO'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 a := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 4) (by simp)
    have a0' : arg (pushed (argPush 5) s₁').callEntry 0 = F.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 5) s₁').callEntry 1 = BitVec.ofNat 32 a := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 5) s₁').callEntry 2 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 5) s₁').callEntry 3 = O.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg' (i := 3) (by simp)
    have a4' : arg (pushed (argPush 5) s₁').callEntry 4 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg' (i := 4) (by simp)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 5) (by decide)
    have eSp' : (pushed (argPush 5) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 5) (by decide)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eSp ⊢
    generalize he' : (pushed (argPush 5) s₁').callEntry = e' at a0' a1' a2' a3' a4' eSp' ⊢
    sig_pub [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a4, a0', a1', a2', a3', a4', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hO' (Lay.okW_iff.mp hO).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 a := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 4) (by simp)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 post
    sig_post [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, a4, m₂, al, bl, ll] at post
    rw [VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 5) (by decide) hF), m] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `f ← BitUnpack(v, a, b)`, of the `len` bytes `v`. -/
theorem bu_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (bitUnpackContract X86.abi 16))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (a b len : Nat) (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b))
    (hs : a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ len < 2 ^ 32) (va vo fa fo : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨va, vo, len⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨fa, fo, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨va, vo, len⟩ ⟨fa, fo, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (toRq (VG.Spec.MlDsa.bitUnpack (bytesAt s.mem (Buf.addr s₀ ⟨va, vo, len⟩) len) a b)) →
      B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP nm c [.buf ⟨va, vo, len⟩, .imm len, .imm a, .imm b, .buf ⟨fa, fo, 1024⟩]) := by
  set V : Buf := ⟨va, vo, len⟩
  set F : Buf := ⟨fa, fo, 1024⟩
  have al : (BitVec.ofNat 32 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  have bl : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  have ll : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hV, hF⟩, dVF⟩ := hc
  have hF' := (Lay.okW_iff.mp hF).1
  refine VG.Proof.MlDsa.X86.Sign.callP_piece _ 5 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hV, hF']) (fun s₀ => [V.rgn s₀])
    (fun s₀ => [F.rgn s₀, below (E1 s₀) 20]) hA
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = V.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 a := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 4) (by simp)
    have eA : argAddr (pushed (argPush 5) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 5) (by decide)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 5) (by decide)
    obtain ⟨rV₁, rV₂, rV₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hV (n := 5) (K := 16) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hF' (n := 5) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 5) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 5) (rd := [V.rgn s₀]) (wr := [F.rgn s₀, below (E1 s₀) 20])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hV h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hF' (Lay.okW_iff.mp hF).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eA eSp ⊢
    sig_pre [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, al, bl, ll]
    exact ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hV hF' dVF, rV₁, rF₁, rV₂, rF₂, rA₂, rV₃, rF₃, rA₃,
      Buf.fit hp hV, Buf.fit hp hF', hab, hl⟩
  · have e₁ : V.ptr s₀ = V.ptr s₀' := hq.t.ptr hV
    have e₂ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = V.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 a := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 4) (by simp)
    have a0' : arg (pushed (argPush 5) s₁').callEntry 0 = V.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 5) s₁').callEntry 1 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 5) s₁').callEntry 2 = BitVec.ofNat 32 a := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 5) s₁').callEntry 3 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg' (i := 3) (by simp)
    have a4' : arg (pushed (argPush 5) s₁').callEntry 4 = F.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg' (i := 4) (by simp)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 5) (by decide)
    have eSp' : (pushed (argPush 5) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 5) (by decide)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eSp ⊢
    generalize he' : (pushed (argPush 5) s₁').callEntry = e' at a0' a1' a2' a3' a4' eSp' ⊢
    sig_pub [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a4, a0', a1', a2', a3', a4', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hF' (Lay.okW_iff.mp hF).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = V.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 a := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = BitVec.ofNat 32 b := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 4) (by simp)
    have b₁ : bytesAt (pushed (argPush 5) s₁).callEntry.mem ((V.ptr s₀).setWidth 64) len = bytesAt s.mem (V.addr s₀) len := by
      rw [← m]; exact VG.Proof.MlKem.bytesAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 5) (by decide) hV)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 post
    sig_post [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, a4, m₂, al, bl, ll] at post
    rw [b₁] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `y ← HintBitPack(h)`, of the hint of `k` polynomials `h`. -/
theorem hbp_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (hintBitPackContract X86.abi 16))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (w k : Nat) (hwk : (w, k) ∈ hintParams) (ha ho oa oo : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨ha, ho, 1024 * k⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨oa, oo, w + k⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨ha, ho, 1024 * k⟩ ⟨oa, oo, w + k⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ hintOnes (hintAt s.mem (Buf.addr s₀ ⟨ha, ho, 1024 * k⟩) k) ≤ w)
    (hleak : ∀ s₀ s₀' s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀' → VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀' → A s₀ s → A s₀' s' →
      (List.range (256 * k)).map (fun i => (coeffAt s.mem (Buf.addr s₀ ⟨ha, ho, 1024 * k⟩) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt s'.mem (Buf.addr s₀' ⟨ha, ho, 1024 * k⟩) i).toNat))
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [⟨oa, oo, w + k⟩] 80) s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, w + k⟩) (w + k) =
        VG.Spec.MlDsa.hintBitPack w k (hintAt s.mem (Buf.addr s₀ ⟨ha, ho, 1024 * k⟩) k) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP nm c [.buf ⟨ha, ho, 1024 * k⟩, .imm (256 * k), .imm w, .buf ⟨oa, oo, w + k⟩, .imm (w + k)]) := by
  set H : Buf := ⟨ha, ho, 1024 * k⟩
  set O : Buf := ⟨oa, oo, w + k⟩
  have hb : w < 100 ∧ k ≤ 8 := by
    simp only [hintParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwk
    rcases hwk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have wl : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat]; omega
  have kl : (BitVec.ofNat 32 (256 * k)).toNat = 256 * k := by rw [BitVec.toNat_ofNat]; omega
  have ll : (BitVec.ofNat 32 (w + k)).toNat = w + k := by rw [BitVec.toNat_ofNat]; omega
  have ek : w + k - w = k := by omega
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hH, hO⟩, dHO⟩ := hc
  have hO' := (Lay.okW_iff.mp hO).1
  refine VG.Proof.MlDsa.X86.Sign.callP_piece _ 5 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hH, hO']) (fun s₀ => [H.rgn s₀])
    (fun s₀ => [O.rgn s₀, below (E1 s₀) 20]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 (256 * k) := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 w := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 (w + k) := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 4) (by simp)
    have eA : argAddr (pushed (argPush 5) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 5) (by decide)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 5) (by decide)
    obtain ⟨rH₁, rH₂, rH₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hH (n := 5) (K := 16) (by decide)
    obtain ⟨rO₁, rO₂, rO₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hO' (n := 5) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 5) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 5) (rd := [H.rgn s₀]) (wr := [O.rgn s₀, below (E1 s₀) 20])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hH h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eA eSp ⊢
    sig_pre [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, wl, kl, ll, ek]
    rw [show 256 * k * 4 = 1024 * k by omega]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hH hO' dHO, rH₁, rO₁, rH₂, rO₂, rA₂, rH₃, rO₃, rA₃,
      Buf.fit hp hH, Buf.fit hp hO', hwk, by omega, trivial, ?_⟩
    rw [VG.Proof.MlDsa.Sign.hintAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 5) (by decide) hH), m]; exact (hA s₀ s hp ha).2
  · have e₁ : H.ptr s₀ = H.ptr s₀' := hq.t.ptr hH
    have e₂ : O.ptr s₀ = O.ptr s₀' := hq.t.ptr hO'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 (256 * k) := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 w := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 (w + k) := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 4) (by simp)
    have a0' : arg (pushed (argPush 5) s₁').callEntry 0 = H.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 5) s₁').callEntry 1 = BitVec.ofNat 32 (256 * k) := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 5) s₁').callEntry 2 = BitVec.ofNat 32 w := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 5) s₁').callEntry 3 = O.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg' (i := 3) (by simp)
    have a4' : arg (pushed (argPush 5) s₁').callEntry 4 = BitVec.ofNat 32 (w + k) := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg' (i := 4) (by simp)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 5) (by decide)
    have eSp' : (pushed (argPush 5) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 5) (by decide)
    have c₁ := coeffs_congr (len := 256 * k) (fun x hx => VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 5) (by decide) hH x (by show x < 1024 * k; omega))
    have c₂ := coeffs_congr (len := 256 * k) (fun x hx => VG.Proof.MlDsa.X86.Sign.ent_bytes hp' h' (n := 5) (by decide) hH x (by show x < 1024 * k; omega))
    have key : (List.range (256 * k)).map (fun i => (coeffAt (pushed (argPush 5) s₁).callEntry.mem (H.addr s₀) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt (pushed (argPush 5) s₁').callEntry.mem (H.addr s₀') i).toNat) := by
      rw [c₁, c₂, m, m']; exact hleak s₀ s₀' s s' hp hp' hq ha ha'
    simp only [Buf.addr, e₁] at key
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eSp key ⊢
    generalize he' : (pushed (argPush 5) s₁').callEntry = e' at a0' a1' a2' a3' a4' eSp' key ⊢
    sig_pub [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a4, a0', a1', a2', a3', a4', eSp, eSp', e₁, e₂, hq.t.E1, and_self,
      kl, key]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hO' (Lay.okW_iff.mp hO).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 (256 * k) := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 w := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 (w + k) := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 4) (by simp)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 post
    sig_post [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a2, a3, a4, m₂, wl, ll, ek] at post
    rw [VG.Proof.MlDsa.Sign.hintAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 5) (by decide) hH), m] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseD`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the private key, and `ρ″`

`ŝ₁`, `ŝ₂` and `t̂₀` are the `NTT` of the `BitUnpack` of their pieces of `sk`
(`decOne_piece`), in the slots from `s1B`, `s2B` and `t0B`, next to `Â`
(`DK`); then `K ‖ rnd` is copied to `HIN`, and `ρ″ = H(K ‖ rnd ‖ μ, 64)`
hashed to `MS` (`KD`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

section
variable (p : Params)

/-- The values of `ŝ₁`, `ŝ₂` and `t̂₀`, from the initial state. -/
abbrev S1 (s₀ : State) : Nat → VG.Spec.MlDsa.Poly := s1F p (VG.Proof.MlDsa.X86.Sign.skOf p s₀)
abbrev S2 (s₀ : State) : Nat → VG.Spec.MlDsa.Poly := s2F p (VG.Proof.MlDsa.X86.Sign.skOf p s₀)
abbrev T0 (s₀ : State) : Nat → VG.Spec.MlDsa.Poly := t0F p (VG.Proof.MlDsa.X86.Sign.skOf p s₀)

/-- `ρ″`, from the initial state. -/
abbrev rppS (s₀ : State) : List Byte := rppV (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀)

/-- `Â`, and the first `n1`, `n2` and `n0` polynomials of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
structure DK (n1 n2 n0 : Nat) (s₀ : State) (m : Mem) : Prop where
  fa : VG.Proof.MlDsa.X86.Sign.Fam s₀ m (VG.Proof.MlDsa.X86.Sign.aBase p) (p.k * p.ℓ) (VG.Proof.MlDsa.X86.Sign.aVal p s₀)
  f1 : VG.Proof.MlDsa.X86.Sign.Fam s₀ m (VG.Proof.MlDsa.X86.Sign.s1B p) n1 (VG.Proof.MlDsa.X86.Sign.S1 p s₀)
  f2 : VG.Proof.MlDsa.X86.Sign.Fam s₀ m (VG.Proof.MlDsa.X86.Sign.s2B p) n2 (VG.Proof.MlDsa.X86.Sign.S2 p s₀)
  f0 : VG.Proof.MlDsa.X86.Sign.Fam s₀ m (VG.Proof.MlDsa.X86.Sign.t0B p) n0 (VG.Proof.MlDsa.X86.Sign.T0 p s₀)

/-- What the loop needs of the setup. -/
structure KD (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s
  dk : VG.Proof.MlDsa.X86.Sign.DK p p.ℓ p.k p.k s₀ s.mem
  ms : bytesAt s.mem (Buf.addr s₀ (sc oMS 64)) 64 = VG.Proof.MlDsa.X86.Sign.rppS p s₀

end

theorem DK.keep {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {n1 n2 n0 : Nat} (h1 : n1 ≤ p.ℓ) (h2 : n2 ≤ p.k)
    (h0 : n0 ≤ p.k) {bs : List Buf} {N : Nat} (hN : N ≤ 80) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m')
    (h : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.OutK p n1 n2 n0 c) (d : VG.Proof.MlDsa.X86.Sign.DK p n1 n2 n0 s₀ m) : VG.Proof.MlDsa.X86.Sign.DK p n1 n2 n0 s₀ m' :=
  ⟨d.fa.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.aBase]; omega) fun c hc => (h c hc).1,
    d.f1.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.s1B]; omega) fun c hc => (h c hc).2.1,
    d.f2.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.s2B]; omega) fun c hc => (h c hc).2.2.1,
    d.f0.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.t0B]; omega) fun c hc => (h c hc).2.2.2⟩

/-! ## A polynomial of the private key -/

/-- The bytes `sk[o : o + l]`. -/
theorem sk_slice {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {o l : Nat} (hol : o + l ≤ p.skLen)
    (hl : 0 < l) : bytesAt s.mem (Buf.addr s₀ (bSk o l)) l = ((VG.Proof.MlDsa.X86.Sign.skOf p s₀).drop o).take l := by
  have ok : (VG.Proof.MlDsa.X86.Sign.Y p).ok (bSk o l) = true :=
    Lay.ok_iff.mpr ⟨by rw [VG.Proof.MlDsa.X86.Sign.Y_n]; exact (by decide : 0 < 5), hl, by rw [VG.Proof.MlDsa.X86.Sign.Y_alen0]; exact hol⟩
  have ok0 : (VG.Proof.MlDsa.X86.Sign.Y p).ok (bSk 0 p.skLen) = true :=
    Lay.ok_iff.mpr ⟨by rw [VG.Proof.MlDsa.X86.Sign.Y_n]; exact (by decide : 0 < 5), by show 0 < p.skLen; omega,
      by rw [VG.Proof.MlDsa.X86.Sign.Y_alen0]; show 0 + p.skLen ≤ p.skLen; omega⟩
  rw [h.roBytes hp ok rfl, VG.Proof.MlKem.bytesAt_slice _ _ hol, Buf.addr_eq hp ok, Buf.addr_eq hp ok0]
  simp only [BitVec.add_zero]

/-- `f ← NTT(BitUnpack(sk[o : o + len], a, b))`, in slot `j`. -/
theorem decOne_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {A B : State → State → Prop} (j o len a b : Nat)
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hs : a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ len < 2 ^ 32)
    (hj : j < VG.Proof.MlDsa.X86.Sign.nS p) (hol : o + len ≤ p.skLen) (hlen : 0 < len)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' →
      Frame (FR s₀ [pS j, sc oPS 1024] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ (pS j)) (VG.Spec.MlDsa.ntt (toRq (VG.Spec.MlDsa.bitUnpack (((VG.Proof.MlDsa.X86.Sign.skOf p s₀).drop o).take len) a b))) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (.seq (bitUnpackAt P (bSk o len) a b (pS j)) (nttAt P (pS j))) := by
  have hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨0, o, len⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨SC, VG.Impl.MlDsa.X86.Sign.oP j, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨0, o, len⟩ ⟨SC, VG.Impl.MlDsa.X86.Sign.oP j, 1024⟩) = true := by
    have := VG.Proof.MlDsa.X86.Sign.slot_ok ps hj
    simp only [Bool.and_eq_true, this, and_true]
    exact ⟨Lay.ok_iff.mpr ⟨by rw [VG.Proof.MlDsa.X86.Sign.Y_n]; exact (by decide : 0 < 5), hlen, by rw [VG.Proof.MlDsa.X86.Sign.Y_alen0]; exact hol⟩, Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)⟩
  refine Piece.seq (B := fun s₀ s₁ => ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s₁ ∧ Frame (FR s₀ [pS j, sc oPS 1024] 80) s.mem s₁.mem ∧
      PolyIs s₁.mem (Buf.addr s₀ (pS j)) (toRq (VG.Spec.MlDsa.bitUnpack (((VG.Proof.MlDsa.X86.Sign.skOf p s₀).drop o).take len) a b)))
    (VG.Proof.MlDsa.X86.Sign.bu_piece F.bitUnpack (F.ok _ (by simp)) a b len hab hl hs 0 o SC (VG.Impl.MlDsa.X86.Sign.oP j) hc hA
      fun s₀ s s' hp ha c' fr hq => ⟨s, ha, c', fr.mono (by simp), by rw [← VG.Proof.MlDsa.X86.Sign.sk_slice hp (hA _ _ hp ha) hol hlen]; exact hq⟩) ?_
  refine VG.Proof.MlDsa.X86.Sign.inPlace_piece (t := VG.Spec.MlDsa.ntt) F.ntt (F.ok _ (by simp)) (pS j) rfl (by
      have := VG.Proof.MlDsa.X86.Sign.slot_ok ps hj; have := VG.Proof.MlDsa.X86.Sign.sc_ok ps (o := oPS) (n := 1024) (by decide) (by decide)
      simp only [Bool.and_eq_true, *, true_and]; ofs)
    (fun s₀ s₁ hp ⟨_, _, c, _, hq⟩ => ⟨c, hq.1⟩) fun s₀ s₁ s' hp ⟨s, ha, c, fr, hq⟩ c' fr' post => ?_
  rw [hq.2] at post
  exact hQ s₀ s s' hp ha c' (fr.trans fr') post

/-! ## The private key -/

theorem ps_sk (ps : VG.Proof.MlDsa.X86.Sign.PS p) : sLen p * p.ℓ + sLen p * p.k + 416 * p.k + 128 = p.skLen := by
  rw [ps.hskLen, Nat.mul_add]; omega

theorem ps_sLen (ps : VG.Proof.MlDsa.X86.Sign.PS p) : 0 < sLen p ∧ sLen p < 2 ^ 32 := by rcases ps.hsLen with h | h <;> omega

/-- `ŝ₁`. -/
theorem decS1s_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p 0 0 0 s₀ s.mem) (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p p.ℓ 0 0 s₀ s.mem)
      (seqR (decS1 P p) 0 p.ℓ) := by
  have := VG.Proof.MlDsa.X86.Sign.seqR_piece (p := p) (f := decS1 P p) (I := fun r s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p r 0 0 s₀ s.mem) 0 p.ℓ
    fun r _ hr => by
      have hl := VG.Proof.MlDsa.X86.Sign.ps_sLen ps
      have hk := VG.Proof.MlDsa.X86.Sign.ps_sk ps
      have hr' : r < p.ℓ := by omega
      have hmul : sLen p * r + sLen p ≤ sLen p * p.ℓ := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr'
      exact VG.Proof.MlDsa.X86.Sign.decOne_piece F ps (VG.Proof.MlDsa.X86.Sign.s1B p + r) (skS1 p r) (sLen p) p.η p.η ps.hη.1 ps.hη.2.1
        ⟨ps.hη.2.2, ps.hη.2.2, hl.2⟩ (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.s1B]; omega) (by simp only [skS1]; omega) hl.1
        (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hq => ⟨c',
          { (h.2.keep hp ps (by omega) (by omega) (by omega) (by decide) fr (by ofs)) with
            f1 := (h.2.f1.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.s1B]; omega) (by ofs)).snoc hq }⟩
  simpa using this

/-- `ŝ₂`. -/
theorem decS2s_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p p.ℓ 0 0 s₀ s.mem) (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p p.ℓ p.k 0 s₀ s.mem)
      (seqR (decS2 P p) 0 p.k) := by
  have := VG.Proof.MlDsa.X86.Sign.seqR_piece (p := p) (f := decS2 P p) (I := fun r s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p p.ℓ r 0 s₀ s.mem) 0 p.k
    fun r _ hr => by
      have hl := VG.Proof.MlDsa.X86.Sign.ps_sLen ps
      have hk := VG.Proof.MlDsa.X86.Sign.ps_sk ps
      have hr' : r < p.k := by omega
      have hmul : sLen p * r + sLen p ≤ sLen p * p.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr'
      exact VG.Proof.MlDsa.X86.Sign.decOne_piece F ps (VG.Proof.MlDsa.X86.Sign.s2B p + r) (skS2 p r) (sLen p) p.η p.η ps.hη.1 ps.hη.2.1
        ⟨ps.hη.2.2, ps.hη.2.2, hl.2⟩ (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.s2B]; omega) (by simp only [skS2]; omega) hl.1
        (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hq => ⟨c',
          { (h.2.keep hp ps (Nat.le_refl _) (by omega) (by omega) (by decide) fr (by ofs)) with
            f2 := (h.2.f2.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.s2B]; omega) (by ofs)).snoc hq }⟩
  simpa using this

theorem t0F_eq (sk : List Byte) (i : Nat) :
    t0F p sk i = VG.Spec.MlDsa.ntt (toRq (VG.Spec.MlDsa.bitUnpack ((sk.drop (skT0 p i)).take 416) 4095 4096)) := by
  unfold t0F
  rw [show 128 + lenS p * p.ℓ + lenS p * p.k + 32 * d * i = skT0 p i by
    simp only [skT0, lenS, sLen, Nat.mul_add, d]; omega]
  rfl

/-- `t̂₀`. -/
theorem decT0s_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p p.ℓ p.k 0 s₀ s.mem) (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p p.ℓ p.k p.k s₀ s.mem)
      (seqR (decT0 P p) 0 p.k) := by
  have := VG.Proof.MlDsa.X86.Sign.seqR_piece (p := p) (f := decT0 P p) (I := fun r s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p p.ℓ p.k r s₀ s.mem) 0 p.k
    fun r _ hr => by
      have hk := VG.Proof.MlDsa.X86.Sign.ps_sk ps
      have hr' : r < p.k := by omega
      have hmul : 416 * r + 416 ≤ 416 * p.k := by omega
      exact VG.Proof.MlDsa.X86.Sign.decOne_piece F ps (VG.Proof.MlDsa.X86.Sign.t0B p + r) (skT0 p r) 416 4095 4096 ps.ht0.1 ps.ht0.2
        ⟨by decide, by decide, by decide⟩ (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.t0B]; omega) (by simp only [skT0, Nat.mul_add]; omega) (by decide)
        (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hq => ⟨c',
          { (h.2.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (by omega) (by decide) fr (by ofs)) with
            f0 := (h.2.f0.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.t0B]; omega) (by ofs)).snoc
              (by show PolyIs _ _ (t0F p _ r); rw [VG.Proof.MlDsa.X86.Sign.t0F_eq]; exact hq) }⟩
  simpa using this

/-! ## `ρ″` -/

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`, with `K ‖ rnd` copied to `HIN` first. -/
theorem rpp_piece (ps : VG.Proof.MlDsa.X86.Sign.PS p) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p p.ℓ p.k p.k s₀ s.mem) (VG.Proof.MlDsa.X86.Sign.KD p)
      (.seq (copyW SC (bSk 32 32) (sc oHIN 32) 8) (.seq (copyW SC bRnd (sc (oHIN + 32) 32) 8)
        (shake2 (sc oHIN 64) bMu (sc oMS 64)))) := by
  have hk := VG.Proof.MlDsa.X86.Sign.ps_sk ps
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p p.ℓ p.k p.k s₀ s.mem ∧
      bytesAt s.mem (Buf.addr s₀ (sc oHIN 32)) 32 = ((VG.Proof.MlDsa.X86.Sign.skOf p s₀).drop 32).take 32)
    (VG.Proof.MlDsa.X86.Sign.copy_piece 0 32 SC oHIN 8 (by decide) (by decide) (by ofs) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h c' fr hb => ⟨c', h.2.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (N := 80)
        (by decide) (show Frame (FR s₀ [sc oHIN 32] 80) s.mem s'.mem from fr.mono (by simp)) (by ofs), by
          show bytesAt s'.mem (Buf.addr s₀ ⟨SC, oHIN, 4 * 8⟩) (4 * 8) = _
          rw [hb]; exact VG.Proof.MlDsa.X86.Sign.sk_slice hp h.1 (by omega) (by decide)⟩) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p p.ℓ p.k p.k s₀ s.mem ∧
      bytesAt s.mem (Buf.addr s₀ (sc oHIN 64)) 64 = ((VG.Proof.MlDsa.X86.Sign.skOf p s₀).drop 32).take 32 ++ VG.Proof.MlDsa.X86.Sign.rndOf s₀)
    (VG.Proof.MlDsa.X86.Sign.copy_piece 2 0 SC (oHIN + 32) 8 (by decide) (by decide) (by ofs) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h c' fr hb => ⟨c', h.2.1.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (N := 80)
        (by decide) (show Frame (FR s₀ [sc (oHIN + 32) 32] 80) s.mem s'.mem from fr.mono (by simp)) (by ofs), by
          rw [bytes_split hp s'.mem (o' := oHIN + 32) (l₁ := 32) (l₂ := 32) rfl rfl (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide))
            (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)), VG.Proof.MlDsa.X86.Sign.keepB hp (N := 80) (by decide) (show Frame (FR s₀ [sc (oHIN + 32) 32] 80) s.mem s'.mem from fr.mono (by simp))
            (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs), h.2.2]
          have : bytesAt s'.mem (Buf.addr s₀ ⟨SC, oHIN + 32, 4 * 8⟩) (4 * 8) = _ := hb
          rw [this, h.1.roBytes hp (b := ⟨2, 0, 4 * 8⟩) (by ofs) rfl]⟩) ?_
  refine VG.Proof.MlDsa.X86.Sign.hash2_piece' 136 0x1f (sc oHIN 64) bMu (sc oMS 64) (by decide) (by ofs) (by decide) (by decide) (by decide)
    (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hb => ⟨c', h.2.1.keep hp ps (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (by decide) fr (by ofs), ?_⟩
  have e : BitVec.setWidth 8 (31#32) = Spec.Sha3.shakeSuffix := by decide
  rw [hb, h.2.2, h.1.roBytes hp (b := bMu) (by ofs) rfl, e, VG.Proof.MlDsa.X86.Sign.rppS, rppV, VG.Proof.MlDsa.Sample.H_eq]

/-- The setup after `ExpandA`. -/
theorem decode_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.DK p 0 0 0 s₀ s.mem) (VG.Proof.MlDsa.X86.Sign.KD p) (decode P p) :=
  (VG.Proof.MlDsa.X86.Sign.decS1s_piece F ps).seq ((VG.Proof.MlDsa.X86.Sign.decS2s_piece F ps).seq ((VG.Proof.MlDsa.X86.Sign.decT0s_piece F ps).seq (VG.Proof.MlDsa.X86.Sign.rpp_piece ps)))

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimC`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): calls of the rounding and hint primitives

`HighBits` and `LowBits` of a polynomial (`hb_piece`, `lb_piece`), the norm
check (`norm_piece`) and `MakeHint` (`hint_piece`), which return their results
in `eax`.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {A B : State → State → Prop}

theorem gamma2_lt {g : Nat} (h : g ∈ gamma2s) : (BitVec.ofNat 32 g).toNat = g := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> rfl

/-- `out ← HighBits(r)`. -/
theorem hb_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (highBitsContract X86.abi 16))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (g : Nat) (hγ : g ∈ gamma2s) (ra ro oa oo : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨ra, ro, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨oa, oo, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨ra, ro, 1024⟩ ⟨oa, oo, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [⟨oa, oo, 1024⟩] 80) s.mem s'.mem →
      NatPolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        ((polyAt s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩)).map fun c => (VG.Spec.MlDsa.highBits g c).toNat) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP nm c [.buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨oa, oo, 1024⟩]) := by
  set R : Buf := ⟨ra, ro, 1024⟩
  set O : Buf := ⟨oa, oo, 1024⟩
  have gl := VG.Proof.MlDsa.X86.Sign.gamma2_lt hγ
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hR, hO⟩, dRO⟩ := hc
  have hO' := (Lay.okW_iff.mp hO).1
  refine VG.Proof.MlDsa.X86.Sign.callP_piece _ 3 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hR, hO']) (fun s₀ => [R.rgn s₀])
    (fun s₀ => [O.rgn s₀, below (E1 s₀) 12]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    have eA : argAddr (pushed (argPush 3) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 3) (by decide)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 3) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hR (n := 3) (K := 16) (by decide)
    obtain ⟨rO₁, rO₂, rO₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hO' (n := 3) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 3) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 3) (rd := [R.rgn s₀]) (wr := [O.rgn s₀, below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hR h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eA eSp ⊢
    sig_pre [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp, gl]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hR hO' dRO, rR₁, rO₁, rR₂, rO₂, rA₂, rR₃, rO₃, rA₃,
      Buf.fit hp hR, Buf.fit hp hO', hγ, ?_⟩
    exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hR) (m ▸ (hA s₀ s hp ha).2)
  · have e₁ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR
    have e₂ : O.ptr s₀ = O.ptr s₀' := hq.t.ptr hO'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    have a0' : arg (pushed (argPush 3) s₁').callEntry 0 = R.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 3) s₁').callEntry 1 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 3) s₁').callEntry 2 = O.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 2) (by simp)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 3) (by decide)
    have eSp' : (pushed (argPush 3) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 3) (by decide)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eSp ⊢
    generalize he' : (pushed (argPush 3) s₁').callEntry = e' at a0' a1' a2' eSp' ⊢
    sig_pub [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a0', a1', a2', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hO' (Lay.okW_iff.mp hO).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 post
    sig_post [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, m₂, gl] at post
    rw [VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hR), m] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `out ← LowBits(r)`, in `R_q`. -/
theorem lb_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (lowBitsContract X86.abi 16))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (g : Nat) (hγ : g ∈ gamma2s) (ra ro oa oo : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨ra, ro, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨oa, oo, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨ra, ro, 1024⟩ ⟨oa, oo, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [⟨oa, oo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        ((polyAt s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩)).map fun c => ofInt (VG.Spec.MlDsa.lowBits g c)) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callP nm c [.buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨oa, oo, 1024⟩]) := by
  set R : Buf := ⟨ra, ro, 1024⟩
  set O : Buf := ⟨oa, oo, 1024⟩
  have gl := VG.Proof.MlDsa.X86.Sign.gamma2_lt hγ
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hR, hO⟩, dRO⟩ := hc
  have hO' := (Lay.okW_iff.mp hO).1
  refine VG.Proof.MlDsa.X86.Sign.callP_piece _ 3 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hR, hO']) (fun s₀ => [R.rgn s₀])
    (fun s₀ => [O.rgn s₀, below (E1 s₀) 12]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    have eA : argAddr (pushed (argPush 3) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 3) (by decide)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 3) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hR (n := 3) (K := 16) (by decide)
    obtain ⟨rO₁, rO₂, rO₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hO' (n := 3) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 3) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 3) (rd := [R.rgn s₀]) (wr := [O.rgn s₀, below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hR h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eA eSp ⊢
    sig_pre [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp, gl]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hR hO' dRO, rR₁, rO₁, rR₂, rO₂, rA₂, rR₃, rO₃, rA₃,
      Buf.fit hp hR, Buf.fit hp hO', hγ, ?_⟩
    exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hR) (m ▸ (hA s₀ s hp ha).2)
  · have e₁ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR
    have e₂ : O.ptr s₀ = O.ptr s₀' := hq.t.ptr hO'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    have a0' : arg (pushed (argPush 3) s₁').callEntry 0 = R.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 3) s₁').callEntry 1 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 3) s₁').callEntry 2 = O.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 2) (by simp)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 3) (by decide)
    have eSp' : (pushed (argPush 3) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 3) (by decide)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eSp ⊢
    generalize he' : (pushed (argPush 3) s₁').callEntry = e' at a0' a1' a2' eSp' ⊢
    sig_pub [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a0', a1', a2', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hO' (Lay.okW_iff.mp hO).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 post
    sig_post [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, m₂, gl] at post
    rw [VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 3) (by decide) hR), m] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `eax ← ‖f‖∞ < bound`. -/
theorem norm_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (normLtContract X86.abi 16))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (bnd : Nat) (hb : bnd < 2 ^ 32) (fa fo : Nat) (hc : (VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨fa, fo, 1024⟩ = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [] 80) s.mem s'.mem →
      s'.gpr .eax = (if normRq [polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)] < bnd then 1 else 0) → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callPR nm c [.buf ⟨fa, fo, 1024⟩, .imm bnd]) := by
  set F : Buf := ⟨fa, fo, 1024⟩
  have bl : (BitVec.ofNat 32 bnd).toNat = bnd := by rw [BitVec.toNat_ofNat]; omega
  refine VG.Proof.MlDsa.X86.Sign.callPR_piece _ 2 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hc]) (fun s₀ => [F.rgn s₀, below (E1 s₀) 8])
    (fun _ => []) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => absurd hr List.not_mem_nil) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = BitVec.ofNat 32 bnd := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 1) (by simp)
    have eA : argAddr (pushed (argPush 2) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 2) (by decide)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 2) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hc (n := 2) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 2) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := VG.Proof.MlDsa.X86.Sign.covers_ro (s := s₁) (n := 2) (rd := [F.rgn s₀, below (E1 s₀) 8]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.within hp hc h.rd h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eA eSp ⊢
    sig_pre [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rF₂, rA₂, rF₃, rA₃, Buf.fit hp hc, ?_⟩
    exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 2) (by decide) hc) (m ▸ (hA s₀ s hp ha).2)
  · have e₁ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hc
    refine ⟨by simp only [Buf.rgn, e₁, hq.t.E1], rfl, ?_⟩
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = BitVec.ofNat 32 bnd := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 1) (by simp)
    have a0' : arg (pushed (argPush 2) s₁').callEntry 0 = F.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .imm bnd]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 2) s₁').callEntry 1 = BitVec.ofNat 32 bnd := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf F, .imm bnd]) (by simp) hg' (i := 1) (by simp)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 2) (by decide)
    have eSp' : (pushed (argPush 2) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 2) (by decide)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eSp ⊢
    generalize he' : (pushed (argPush 2) s₁').callEntry = e' at a0' a1' eSp' ⊢
    sig_pub [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a0', a1', eSp, eSp', e₁, hq.t.E1, and_self]
  · obtain ⟨s₂, m₂, g₂, post⟩ := post
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = BitVec.ofNat 32 bnd := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 1) (by simp)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 post
    sig_post [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, VG.Proof.MlDsa.X86.Sign.sw32, g₂, bl] at post
    rw [VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 2) (by decide) hc), m] at post
    refine hQ s₀ s s' hp ha h' ((m ▸ fr).sub fun r hr => ?_) post
    simp only [List.nil_append, List.mem_singleton] at hr; subst hr
    exact ⟨below (E1 s₀) 80, by simp [FR], stk_sub hp (by have := ok.stk; omega) (by show 80 + 16 ≤ 96; omega)⟩

/-- `h ← MakeHint(z, r)`, returning the number of 1s in `eax`. -/
theorem hint_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (makeHintContract X86.abi 16))
    (ok : VG.Proof.MlDsa.X86.Sign.COk c) (g : Nat) (hγ : g ∈ gamma2s) (za zo ra ro ha ho : Nat)
    (hc : ((VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨za, zo, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).ok ⟨ra, ro, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).okW ⟨ha, ho, 1024⟩ &&
      (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨za, zo, 1024⟩ ⟨ha, ho, 1024⟩ && (VG.Proof.MlDsa.X86.Sign.Y p).sep ⟨ra, ro, 1024⟩ ⟨ha, ho, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨za, zo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → Frame (FR s₀ [⟨ha, ho, 1024⟩] 80) s.mem s'.mem →
      HintIs s'.mem (Buf.addr s₀ ⟨ha, ho, 1024⟩) 1 [Vector.zipWith (VG.Spec.MlDsa.makeHint g) (polyAt s.mem (Buf.addr s₀ ⟨za, zo, 1024⟩))
        (polyAt s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))] →
      (s'.gpr .eax).toNat = hintOnes [Vector.zipWith (VG.Spec.MlDsa.makeHint g) (polyAt s.mem (Buf.addr s₀ ⟨za, zo, 1024⟩))
        (polyAt s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))] → B s₀ s') :
    VG.Proof.MlDsa.X86.Sign.SP p A B (callPR nm c [.buf ⟨za, zo, 1024⟩, .buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨ha, ho, 1024⟩]) := by
  set Z : Buf := ⟨za, zo, 1024⟩
  set R : Buf := ⟨ra, ro, 1024⟩
  set H : Buf := ⟨ha, ho, 1024⟩
  have gl := VG.Proof.MlDsa.X86.Sign.gamma2_lt hγ
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hZ, hR⟩, hH⟩, dZH⟩, dRH⟩ := hc
  have hH' := (Lay.okW_iff.mp hH).1
  refine VG.Proof.MlDsa.X86.Sign.callPR_piece _ 4 rfl hv ok (by decide) (by decide) (by simp [VG.Proof.MlDsa.X86.Sign.argOk, hZ, hR, hH']) (fun s₀ => [Z.rgn s₀, R.rgn s₀])
    (fun s₀ => [H.rgn s₀, below (E1 s₀) 16]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = Z.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 3) (by simp)
    have eA : argAddr (pushed (argPush 4) s₁).callEntry 0 = _ := VG.Proof.MlDsa.X86.Sign.ent_arg0 h (n := 4) (by decide)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 4) (by decide)
    obtain ⟨rZ₁, rZ₂, rZ₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hZ (n := 4) (K := 16) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hR (n := 4) (K := 16) (by decide)
    obtain ⟨rH₁, rH₂, rH₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_rgn hp hH' (n := 4) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlDsa.X86.Sign.ent_self hp (n := 4) (K := 16) (by decide)
    have hE := VG.Proof.MlDsa.X86.Sign.E1_big hp
    have cv := covers_of (s := s₁) (n := 4) (rd := [Z.rgn s₀, R.rgn s₀]) (wr := [H.rgn s₀, below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Buf.within hp hZ h.rd h.wr
        · exact Buf.within hp hR h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hH' (Lay.okW_iff.mp hH).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eA eSp ⊢
    sig_pre [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, gl]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hZ hH' dZH, rZ₁, Buf.disj hp hR hH' dRH, rR₁, rH₁, rZ₂, rR₂, rH₂, rA₂, rZ₃, rR₃, rH₃, rA₃,
      Buf.fit hp hZ, Buf.fit hp hR, Buf.fit hp hH', hγ, ?_, ?_⟩
    · exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 4) (by decide) hZ) (m ▸ (hA s₀ s hp ha).2.1)
    · exact VG.Proof.MlDsa.Sign.reduced_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 4) (by decide) hR) (m ▸ (hA s₀ s hp ha).2.2)
  · have e₁ : Z.ptr s₀ = Z.ptr s₀' := hq.t.ptr hZ
    have e₂ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR
    have e₃ : H.ptr s₀ = H.ptr s₀' := hq.t.ptr hH'
    refine ⟨by simp only [Buf.rgn, e₁, e₂], by simp only [Buf.rgn, e₃, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = Z.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 3) (by simp)
    have a0' : arg (pushed (argPush 4) s₁').callEntry 0 = Z.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 4) s₁').callEntry 1 = R.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 4) s₁').callEntry 2 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 4) s₁').callEntry 3 = H.ptr s₀' := VG.Proof.MlDsa.X86.Sign.ent_arg hp' h' (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg' (i := 3) (by simp)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h (n := 4) (by decide)
    have eSp' : (pushed (argPush 4) s₁').callEntry.gpr .esp = _ := VG.Proof.MlDsa.X86.Sign.ent_esp h' (n := 4) (by decide)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eSp ⊢
    generalize he' : (pushed (argPush 4) s₁').callEntry = e' at a0' a1' a2' a3' eSp' ⊢
    sig_pub [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a0', a1', a2', a3', eSp, eSp', e₁, e₂, e₃, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hH' (Lay.okW_iff.mp hH).2
    · exact VG.Proof.MlDsa.X86.Sign.stk_W hp (by decide)
  · obtain ⟨s₂, m₂, g₂, post⟩ := post
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = Z.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = R.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = BitVec.ofNat 32 g := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = H.ptr s₀ := VG.Proof.MlDsa.X86.Sign.ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 3) (by simp)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 post
    sig_post [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, VG.Proof.MlDsa.X86.Sign.sw32, g₂, gl] at post
    rw [VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 4) (by decide) hZ), VG.Proof.MlDsa.Sign.polyAt_congr (VG.Proof.MlDsa.X86.Sign.ent_bytes hp h (n := 4) (by decide) hR),
      m] at post
    exact hQ s₀ s s' hp ha h' (VG.Proof.MlDsa.X86.Sign.fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post.1 post.2

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseC`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the commitment of an iteration

Iteration `t` of the loop (`IT`: the setup, `κ = ℓt` at `KAP` and `814 - t` at
`CNT`) computes `y = ExpandMask(ρ″, κ)` and `ŷ = NTT(y)` (`maskR_piece`), `w =
NTT⁻¹(Â ŷ)` (`rowW_piece`), the encoding of `w₁ = HighBits(w)` at `W1`
(`w1R_piece`), and `c̃ = H(μ ‖ w1Encode(w₁), λ/4)` at `CT` (`commit_piece`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_shr)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

section
variable (p : Params)

/-- `Â`, `y`, `ŷ`, `w` and `c̃` of the iteration with counter `κ`. -/
abbrev Am (s₀ : State) : Nat → Nat → VG.Spec.MlDsa.Poly := Av (VG.Proof.MlDsa.X86.Sign.skOf p s₀)
abbrev Yv (s₀ : State) (κ r : Nat) : VG.Spec.MlDsa.Poly := toRq (yF p (VG.Proof.MlDsa.X86.Sign.rppS p s₀) κ r)
abbrev YHv (s₀ : State) (κ r : Nat) : VG.Spec.MlDsa.Poly := yhF p (VG.Proof.MlDsa.X86.Sign.rppS p s₀) κ r
abbrev Wv (s₀ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := wF p (VG.Proof.MlDsa.X86.Sign.Am p s₀) (VG.Proof.MlDsa.X86.Sign.rppS p s₀) κ i
abbrev CTv (s₀ : State) (κ : Nat) : List Byte := ctF p (VG.Proof.MlDsa.X86.Sign.Am p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rppS p s₀) κ

/-- Iteration `t`, on entry. -/
structure IT (t : Nat) (s₀ s : State) : Prop where
  kd : VG.Proof.MlDsa.X86.Sign.KD p s₀ s
  kap : VG.Proof.MlDsa.X86.Sign.scw s₀ s oKAP = BitVec.ofNat 32 (p.ℓ * t)
  cnt : VG.Proof.MlDsa.X86.Sign.scw s₀ s oCNT = BitVec.ofNat 32 (814 - t)
  lt : t < 814

end

theorem IT.keep {t : Nat} {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.IT p t s₀ s)
    (c' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s') {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.OutI p c) : VG.Proof.MlDsa.X86.Sign.IT p t s₀ s' :=
  ⟨⟨c', h.kd.dk.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hN fr fun c hc => (hb c hc).1,
    by rw [VG.Proof.MlDsa.X86.Sign.keepB hp hN fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2.2, h.kd.ms]⟩,
    by rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp hN fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun c hc => ⟨(hb c hc).2.1.1, fun e => by
      have := (hb c hc).2.1.2 e; simp only [oCNT, oKAP] at this ⊢; omega⟩]; exact h.kap,
    by rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp hN fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun c hc => ⟨(hb c hc).2.1.1, fun e => by
      have := (hb c hc).2.1.2 e; simp only [oCNT, oKAP] at this ⊢; omega⟩]; exact h.cnt, h.lt⟩

theorem aVal_ij {s₀ : State} {i j : Nat} (hj : j < p.ℓ) : VG.Proof.MlDsa.X86.Sign.aVal p s₀ (p.ℓ * i + j) = VG.Proof.MlDsa.X86.Sign.Am p s₀ i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [VG.Proof.MlDsa.X86.Sign.aVal, e1, e2]

/-! ## `y` and `ŷ` -/

theorem integerToBytes_two (x : Nat) : integerToBytes x 2 = [BitVec.ofNat 8 x, BitVec.ofNat 8 (x / 256)] := by
  simp [integerToBytes, List.range_succ]

theorem kap_lt (ps : VG.Proof.MlDsa.X86.Sign.PS p) {t r : Nat} (ht : t < 814) (hr : r < p.ℓ) : p.ℓ * t + r < 2 ^ 16 := by
  have := ps.hl
  have : p.ℓ * t ≤ 7 * 813 := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- Iteration `t`, with the first `r` polynomials of `y` and `ŷ`. -/
structure CM (p : Params) (t r : Nat) (s₀ s : State) : Prop where
  it : VG.Proof.MlDsa.X86.Sign.IT p t s₀ s
  fy : VG.Proof.MlDsa.X86.Sign.Fam s₀ s.mem (VG.Proof.MlDsa.X86.Sign.yB p) r (VG.Proof.MlDsa.X86.Sign.Yv p s₀ (p.ℓ * t))
  fyh : VG.Proof.MlDsa.X86.Sign.Fam s₀ s.mem (VG.Proof.MlDsa.X86.Sign.yhB p) r (VG.Proof.MlDsa.X86.Sign.YHv p s₀ (p.ℓ * t))

/-- `κ + r` to `MS + 64`: the seed of `y[r]` at `MS`. -/
theorem setKappa_piece (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t r : Nat) (hr : r < p.ℓ) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.CM p t r) (fun s₀ s => VG.Proof.MlDsa.X86.Sign.CM p t r s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (sc oMS 66)) 66 = VG.Proof.MlDsa.X86.Sign.rppS p s₀ ++ integerToBytes (p.ℓ * t + r) 2)
      (.block (setKappa r)) := by
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.it.kd.ctx) (fun s₀ s hp hc => ?_) rfl
  have h := hc.it
  have hk := VG.Proof.MlDsa.X86.Sign.kap_lt ps h.lt hr
  unfold setKappa
  refine VG.Proof.MlDsa.X86.Sign.wp_ldsc hp h.kd.ctx (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_addi fun s₂ o₂ v₂ => ?_
  have c₂ := h.kd.ctx.only (o₁.trans o₂) (by simp) (by simp)
  refine VG.Proof.MlDsa.X86.Sign.wp_st8sc hp c₂ (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) fun s₃ c₃ g₃ m₃ => wp_shr (by decide) (by decide)
    fun s₄ o₄ v₄ => ?_
  have c₄ := c₃.only o₄ (by simp) (by simp)
  refine VG.Proof.MlDsa.X86.Sign.wp_st8sc hp c₄ (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) fun s₅ c₅ g₅ m₅ => WP.block_nil_iff.mpr ?_
  have ex : s₂.gpr .eax = BitVec.ofNat 32 (p.ℓ * t + r) := by
    rw [v₂, v₁, h.kap, BitVec.ofNat_add]
  have fr₃ : Frame (FR s₀ [sc (oMS + 64) 1] 0) s.mem s₃.mem := by
    rw [m₃, ← (o₁.trans o₂).mem]; exact frW8 (Y := VG.Proof.MlDsa.X86.Sign.Y p)
  have fr₅ : Frame (FR s₀ [sc (oMS + 65) 1] 0) s₃.mem s₅.mem := by
    rw [m₅, ← o₄.mem]; exact frW8 (Y := VG.Proof.MlDsa.X86.Sign.Y p)
  have fs : ∀ o, o = oMS + 64 ∨ o = oMS + 65 → ∀ c ∈ [sc o 1], c.arg = SC ∧ oMS + 64 ≤ c.off ∧
      c.off + c.len ≤ oMS + 66 ∧ 0 < c.len :=
    fun o ho c hc => by rw [List.mem_singleton] at hc; subst hc; simp only [oMS, true_and] at ho ⊢; omega
  have hhi : oMS + 66 ≤ VG.Proof.MlDsa.X86.Sign.scrLen p := by have := VG.Proof.MlDsa.X86.Sign.scr_ge ps; simp only [VG.Impl.MlDsa.X86.Sign.oP, oMS, VG.Proof.MlDsa.X86.Sign.nS] at this ⊢; omega
  have f := (VG.Proof.MlDsa.X86.Sign.frSc hp (M := 80) (by decide) (by decide) (by decide) hhi (fs _ (.inl rfl)) fr₃).trans
    (VG.Proof.MlDsa.X86.Sign.frSc hp (M := 80) (by decide) (by decide) (by decide) hhi (fs _ (.inr rfl)) fr₅)
  refine ⟨⟨h.keep hp ps c₅ (by decide) f (by ofs), hc.fy.keep hp ps (by decide) f (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) (by ofs),
    hc.fyh.keep hp ps (by decide) f (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yhB]; omega) (by ofs)⟩, ?_⟩
  have b0 : bytesAt s₃.mem (Buf.addr s₀ (sc (oMS + 64) 1)) 1 = [BitVec.ofNat 8 (p.ℓ * t + r)] := by
    rw [m₃, VG.Proof.MlDsa.X86.Sign.bytes1_write]; show [(s₂.gpr .eax).setWidth 8] = _; rw [ex, VG.Proof.MlDsa.X86.Sign.setWidth8_ofNat]
  have b0' : bytesAt s₅.mem (Buf.addr s₀ (sc (oMS + 64) 1)) 1 = [BitVec.ofNat 8 (p.ℓ * t + r)] := by
    rw [VG.Proof.MlDsa.X86.Sign.keepB hp (by decide) fr₅ (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun c hc => by
      rw [List.mem_singleton] at hc; subst hc; exact ⟨VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide), fun _ => .inr (Nat.le_refl _)⟩, b0]
  have b1 : bytesAt s₅.mem (Buf.addr s₀ (sc (oMS + 65) 1)) 1 = [BitVec.ofNat 8 ((p.ℓ * t + r) / 256)] := by
    rw [m₅, VG.Proof.MlDsa.X86.Sign.bytes1_write]; show [(s₄.gpr .eax).setWidth 8] = _; rw [v₄, g₃, ex]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    omega
  have hm : bytesAt s₅.mem (Buf.addr s₀ (sc oMS 64)) 64 = VG.Proof.MlDsa.X86.Sign.rppS p s₀ := by
    rw [VG.Proof.MlDsa.X86.Sign.keepB hp (by decide) f (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs), h.kd.ms]
  rw [bytes_split hp s₅.mem (o' := oMS + 64) (l₁ := 64) (l₂ := 2) rfl rfl (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide))
    (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)), hm,
    bytes_split hp s₅.mem (o' := oMS + 65) (l₁ := 1) (l₂ := 1) rfl rfl (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide))
    (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)), b0', b1, VG.Proof.MlDsa.X86.Sign.integerToBytes_two]
  rfl

/-- `y[r]` and `ŷ[r]`. -/
theorem maskR_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t r : Nat) (hr : r < p.ℓ) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.CM p t r) (VG.Proof.MlDsa.X86.Sign.CM p t (r + 1)) (maskR P p r) := by
  have hj : VG.Proof.MlDsa.X86.Sign.yB p + r < VG.Proof.MlDsa.X86.Sign.nS p := by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega
  have hj' : VG.Proof.MlDsa.X86.Sign.yhB p + r < VG.Proof.MlDsa.X86.Sign.nS p := by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yhB]; omega
  refine (VG.Proof.MlDsa.X86.Sign.setKappa_piece ps t r hr).seq ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CM p t r s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (VG.Proof.MlDsa.X86.Sign.yB p + r))) (VG.Proof.MlDsa.X86.Sign.Yv p s₀ (p.ℓ * t) r))
    (VG.Proof.MlDsa.X86.Sign.mask_piece F.expandMask (F.ok _ (by simp)) p.γ₁ ps.hγ₁ SC oMS SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.yB p + r)) SC oPS (by ofs)
      (fun _ _ _ h => h.1.it.kd.ctx) fun s₀ s s' hp h c' fr hq => ⟨⟨h.1.it.keep hp ps c' (by decide) fr (by ofs),
        h.1.fy.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) (by ofs),
        h.1.fyh.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yhB]; omega) (by ofs)⟩, by rw [h.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CM p t r s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (VG.Proof.MlDsa.X86.Sign.yB p + r))) (VG.Proof.MlDsa.X86.Sign.Yv p s₀ (p.ℓ * t) r) ∧
      PolyIs s.mem (Buf.addr s₀ (pS (VG.Proof.MlDsa.X86.Sign.yhB p + r))) (VG.Proof.MlDsa.X86.Sign.Yv p s₀ (p.ℓ * t) r))
    (VG.Proof.MlDsa.X86.Sign.copy_piece SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.yB p + r)) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.yhB p + r)) 256 (by decide) (by decide) (by ofs)
      (fun _ _ _ h => h.1.it.kd.ctx) fun s₀ s s' hp h c' fr hb => ?_) ?_
  · have fr' : Frame (FR s₀ [pS (VG.Proof.MlDsa.X86.Sign.yhB p + r)] 80) s.mem s'.mem := fr.mono (by simp)
    exact ⟨⟨h.1.it.keep hp ps c' (by decide) fr' (by ofs),
      h.1.fy.keep hp ps (by decide) fr' (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) (by ofs),
      h.1.fyh.keep hp ps (by decide) fr' (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yhB]; omega) (by ofs)⟩,
      VG.Proof.MlDsa.X86.Sign.keepP hp ps (by decide) fr' hj (by ofs) h.2, polyIs_of_bytes hb h.2⟩
  refine VG.Proof.MlDsa.X86.Sign.inPlace_piece (t := VG.Spec.MlDsa.ntt) F.ntt (F.ok _ (by simp)) (pS (VG.Proof.MlDsa.X86.Sign.yhB p + r)) rfl (by ofs)
    (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.2.1⟩) fun s₀ s s' hp h c' fr hq => ?_
  rw [h.2.2.2] at hq
  exact ⟨h.1.it.keep hp ps c' (by decide) fr (by ofs),
    (h.1.fy.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) (by ofs)).snoc (VG.Proof.MlDsa.X86.Sign.keepP hp ps (by decide) fr hj (by ofs) h.2.1),
    (h.1.fyh.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yhB]; omega) (by ofs)).snoc hq⟩

/-! ## `w` -/

/-- `∑_{j < m} Â[i, j] ŷ[j]`, summed from `j = 0` with `AddNTT`. -/
abbrev wAcc (p : Params) (s₀ : State) (κ i m : Nat) : VG.Spec.MlDsa.Poly :=
  ((List.range m).map fun j => multiplyNTT (VG.Proof.MlDsa.X86.Sign.Am p s₀ i j) (VG.Proof.MlDsa.X86.Sign.YHv p s₀ κ j)).foldl VG.Spec.MlDsa.add VG.Spec.MlDsa.zero

theorem add_zero_left (x : VG.Spec.MlDsa.Poly) : VG.Spec.MlDsa.add VG.Spec.MlDsa.zero x = x := by
  apply Vector.ext
  intro j hj
  simp [VG.Spec.MlDsa.add, VG.Spec.MlDsa.zero]

theorem wAcc_one (s₀ : State) (κ i : Nat) :
    VG.Proof.MlDsa.X86.Sign.wAcc p s₀ κ i 1 = multiplyNTT (VG.Proof.MlDsa.X86.Sign.Am p s₀ i 0) (VG.Proof.MlDsa.X86.Sign.YHv p s₀ κ 0) := by
  simp only [VG.Proof.MlDsa.X86.Sign.wAcc, List.range_one, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, VG.Proof.MlDsa.X86.Sign.add_zero_left]

theorem wAcc_succ (s₀ : State) (κ i m : Nat) :
    VG.Proof.MlDsa.X86.Sign.wAcc p s₀ κ i (m + 1) = VG.Spec.MlDsa.add (VG.Proof.MlDsa.X86.Sign.wAcc p s₀ κ i m) (multiplyNTT (VG.Proof.MlDsa.X86.Sign.Am p s₀ i m) (VG.Proof.MlDsa.X86.Sign.YHv p s₀ κ m)) := by
  simp only [VG.Proof.MlDsa.X86.Sign.wAcc, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- Iteration `t`, with `y`, `ŷ` and the first `i` polynomials of `w`. -/
structure CW (p : Params) (t i : Nat) (s₀ s : State) : Prop where
  cm : VG.Proof.MlDsa.X86.Sign.CM p t p.ℓ s₀ s
  fw : VG.Proof.MlDsa.X86.Sign.Fam s₀ s.mem (VG.Proof.MlDsa.X86.Sign.wB p) i (VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t))

theorem CW.keep {t i : Nat} {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.CW p t i s₀ s) (hi : i ≤ p.k)
    (c' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s') {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.OutI p c ∧ VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.yB p)) (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + i)) c) : VG.Proof.MlDsa.X86.Sign.CW p t i s₀ s' :=
  ⟨⟨h.cm.it.keep hp ps c' hN fr fun c hc => (hb c hc).1,
    h.cm.fy.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [VG.Impl.MlDsa.X86.Sign.oP, VG.Proof.MlDsa.X86.Sign.yB, VG.Proof.MlDsa.X86.Sign.wB] at this ⊢; omega⟩,
    h.cm.fyh.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yhB]; omega) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [VG.Impl.MlDsa.X86.Sign.oP, VG.Proof.MlDsa.X86.Sign.yB, VG.Proof.MlDsa.X86.Sign.yhB, VG.Proof.MlDsa.X86.Sign.wB] at this ⊢; omega⟩⟩,
    h.fw.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.wB]; omega) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [VG.Impl.MlDsa.X86.Sign.oP, VG.Proof.MlDsa.X86.Sign.yB, VG.Proof.MlDsa.X86.Sign.wB] at this ⊢; omega⟩⟩

theorem fam_at {s₀ : State} {m : Mem} {b n : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.X86.Sign.Fam s₀ m b n f) {j : Nat} (hj : j < n) :
    PolyIs m (Buf.addr s₀ (pS (b + j))) (f j) := h j hj

/-- `w[i]`. -/
theorem rowW_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t i : Nat) (hi : i < p.k) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.CW p t i) (VG.Proof.MlDsa.X86.Sign.CW p t (i + 1)) (rowW P p i) := by
  have hl := ps.hl
  have hj : VG.Proof.MlDsa.X86.Sign.wB p + i < VG.Proof.MlDsa.X86.Sign.nS p := by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.wB]; omega
  have ha : ∀ j < p.ℓ, p.ℓ * i + j < p.k * p.ℓ := fun j hj => VG.Proof.MlDsa.X86.Sign.aIdx hi hj
  unfold rowW
  simp only [VG.Proof.MlDsa.X86.Sign.aP_eq]
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CW p t i s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (VG.Proof.MlDsa.X86.Sign.wB p + i))) (VG.Proof.MlDsa.X86.Sign.wAcc p s₀ (p.ℓ * t) i 1))
    (VG.Proof.MlDsa.X86.Sign.mul_piece F.mul (F.ok _ (by simp)) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + i)) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.aBase p + (p.ℓ * i + 0))) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.yhB p + 0))
      (by have := ha 0 (by omega); ofs)
      (fun _ _ _ h => ⟨h.cm.it.kd.ctx, (VG.Proof.MlDsa.X86.Sign.fam_at h.cm.it.kd.dk.fa (ha 0 (by omega))).1, (VG.Proof.MlDsa.X86.Sign.fam_at h.cm.fyh (by omega)).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps (by omega) c' (by decide) fr (by ofs), ?_⟩) ?_
  · rw [(VG.Proof.MlDsa.X86.Sign.fam_at h.cm.it.kd.dk.fa (ha 0 (by omega))).2, (VG.Proof.MlDsa.X86.Sign.fam_at h.cm.fyh (by omega)).2, VG.Proof.MlDsa.X86.Sign.aVal_ij (by omega)] at hq
    rw [VG.Proof.MlDsa.X86.Sign.wAcc_one]; exact hq
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CW p t i s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (VG.Proof.MlDsa.X86.Sign.wB p + i))) (VG.Proof.MlDsa.X86.Sign.wAcc p s₀ (p.ℓ * t) i p.ℓ))
    ?_ ?_
  · have := VG.Proof.MlDsa.X86.Sign.seqR_piece (p := p) (I := fun j s₀ s => VG.Proof.MlDsa.X86.Sign.CW p t i s₀ s ∧
        PolyIs s.mem (Buf.addr s₀ (pS (VG.Proof.MlDsa.X86.Sign.wB p + i))) (VG.Proof.MlDsa.X86.Sign.wAcc p s₀ (p.ℓ * t) i j)) 1 (p.ℓ - 1) fun j hj1 hj2 =>
      VG.Proof.MlDsa.X86.Sign.mulAdd_piece (nm := "vg_mldsa_multiply_add_ntt") F.mulAdd (F.ok _ (by simp)) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + i)) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.aBase p + (p.ℓ * i + j))) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.yhB p + j))
        (by have := ha j (by omega); ofs)
        (fun _ _ _ h => ⟨h.1.cm.it.kd.ctx, h.2.1, (VG.Proof.MlDsa.X86.Sign.fam_at h.1.cm.it.kd.dk.fa (ha j (by omega))).1,
          (VG.Proof.MlDsa.X86.Sign.fam_at h.1.cm.fyh (by omega)).1⟩)
        fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps (by omega) c' (by decide) fr (by ofs), by
          rw [h.2.2, (VG.Proof.MlDsa.X86.Sign.fam_at h.1.cm.it.kd.dk.fa (ha j (by omega))).2, (VG.Proof.MlDsa.X86.Sign.fam_at h.1.cm.fyh (by omega)).2,
            VG.Proof.MlDsa.X86.Sign.aVal_ij (by omega)] at hq
          rw [VG.Proof.MlDsa.X86.Sign.wAcc_succ]; exact hq⟩
    rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at this
  refine VG.Proof.MlDsa.X86.Sign.inPlace_piece (t := VG.Spec.MlDsa.nttInv) F.invNtt (F.ok _ (by simp)) (pS (VG.Proof.MlDsa.X86.Sign.wB p + i)) rfl (by ofs)
    (fun _ _ _ h => ⟨h.1.cm.it.kd.ctx, h.2.1⟩) fun s₀ s s' hp h c' fr hq => ?_
  rw [h.2.2] at hq
  exact ⟨(h.1.keep hp ps (by omega) c' (by decide) fr (by ofs)).cm, (h.1.keep hp ps (by omega) c' (by decide) fr
    (by ofs)).fw.snoc hq⟩

/-! ## `w₁` and `c̃` -/

/-- The encodings of the first `i` polynomials of `w₁`. -/
abbrev w1Enc (p : Params) (s₀ : State) (κ i : Nat) : List Byte :=
  (List.range i).flatMap fun j => VG.Spec.MlDsa.simpleBitPack (w1F p (VG.Proof.MlDsa.X86.Sign.Am p s₀) (VG.Proof.MlDsa.X86.Sign.rppS p s₀) κ j) (w1Max p)

/-- Iteration `t`, with `y`, `w`, and the encodings of the first `i` polynomials of `w₁` at `W1`. -/
structure CH (p : Params) (t i : Nat) (s₀ s : State) : Prop where
  cw : VG.Proof.MlDsa.X86.Sign.CW p t p.k s₀ s
  w1 : bytesAt s.mem (Buf.addr s₀ (sc oW1 1024)) (w1Len p * i) = VG.Proof.MlDsa.X86.Sign.w1Enc p s₀ (p.ℓ * t) i

theorem natPolyIs_coeff {m : Mem} {a : Addr} {f : Vector Nat n} (h : NatPolyIs m a f) {j : Nat} (hj : j < 256) :
    (coeffAt m a j).toNat = f[j] := by
  have := congrArg (·[j]) h
  simp only [natPolyAt, Vector.getElem_ofFn] at this
  exact this

/-- `w1Encode(w₁[i])` to `W1 + w1Len · i`. -/
theorem w1R_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t i : Nat) (hi : i < p.k) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.CH p t i) (VG.Proof.MlDsa.X86.Sign.CH p t (i + 1)) (w1R P p i) := by
  have hj : VG.Proof.MlDsa.X86.Sign.wB p + i < VG.Proof.MlDsa.X86.Sign.nS p := by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.wB]; omega
  have hw := ps.hw1
  have hwl : w1Len p * i + w1Len p ≤ 1024 := by
    have : w1Len p * i + w1Len p ≤ w1Len p * p.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    rw [Nat.mul_comm p.k] at hw; omega
  have hwp : 0 < w1Len p := by rcases ps.hw1Len with h | h <;> omega
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CH p t i s₀ s ∧
      NatPolyIs s.mem (Buf.addr s₀ t1P) (w1F p (VG.Proof.MlDsa.X86.Sign.Am p s₀) (VG.Proof.MlDsa.X86.Sign.rppS p s₀) (p.ℓ * t) i))
    (VG.Proof.MlDsa.X86.Sign.hb_piece F.highBits (F.ok _ (by simp)) p.γ₂ ps.hγ₂ SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + i)) SC (VG.Impl.MlDsa.X86.Sign.oP 1) (by ofs)
      (fun _ _ _ h => ⟨h.cw.cm.it.kd.ctx, (VG.Proof.MlDsa.X86.Sign.fam_at h.cw.fw hi).1⟩) fun s₀ s s' hp h c' fr hq =>
      ⟨⟨h.cw.keep hp ps (Nat.le_refl _) c' (by decide) fr (by ofs), by
        rw [VG.Proof.MlDsa.X86.Sign.keepB0 hp (by decide) fr 1024 (by have := VG.Proof.MlDsa.X86.Sign.scr_ge ps; simp only [VG.Impl.MlDsa.X86.Sign.oP, oW1, VG.Proof.MlDsa.X86.Sign.nS] at this ⊢; omega) (by ofs)]
        exact h.w1⟩, by rw [(VG.Proof.MlDsa.X86.Sign.fam_at h.cw.fw hi).2] at hq; exact hq⟩) ?_
  refine VG.Proof.MlDsa.X86.Sign.sbp_piece F.simpleBitPack (F.ok _ (by simp)) (w1Max p) (w1Len p) ps.hw1Max.1 ps.hw1Max.2 SC (VG.Impl.MlDsa.X86.Sign.oP 1) SC
    (oW1 + w1Len p * i) (by ofs) (fun _ _ _ h => ⟨h.1.cw.cm.it.kd.ctx, fun j hj => by
      rw [VG.Proof.MlDsa.X86.Sign.natPolyIs_coeff h.2 hj, w1F, Vector.getElem_map]; exact highBits_le ps.hγ₂ _⟩)
    fun s₀ s s' hp h c' fr hq => ⟨h.1.cw.keep hp ps (Nat.le_refl _) c' (by decide) fr (by ofs), ?_⟩
  have e : Buf.addr s₀ (sc (oW1 + w1Len p * i) (w1Len p)) = Buf.addr s₀ (sc oW1 1024) + BitVec.ofNat 64 (w1Len p * i) :=
    VG.Proof.MlDsa.X86.Sign.addr_off hp (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)
  rw [Nat.mul_succ, VG.Proof.MlKem.bytesAt_add, ← e, hq, h.2,
    VG.Proof.MlDsa.X86.Sign.keepB0 hp (by decide) fr 1024 (by have := VG.Proof.MlDsa.X86.Sign.scr_ge ps; simp only [VG.Impl.MlDsa.X86.Sign.oP, oW1, VG.Proof.MlDsa.X86.Sign.nS] at this ⊢; omega) (by ofs), h.1.w1,
    VG.Proof.MlDsa.X86.Sign.w1Enc, VG.Proof.MlDsa.X86.Sign.w1Enc, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- Iteration `t`, with `y`, `w` and `c̃`. -/
structure CC (p : Params) (t : Nat) (s₀ s : State) : Prop where
  cw : VG.Proof.MlDsa.X86.Sign.CW p t p.k s₀ s
  ct : bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)

theorem w1Enc_eq (s₀ : State) (κ : Nat) :
    VG.Proof.MlDsa.X86.Sign.w1Enc p s₀ κ p.k = w1Encode p ((List.range p.k).map (w1F p (VG.Proof.MlDsa.X86.Sign.Am p s₀) (VG.Proof.MlDsa.X86.Sign.rppS p s₀) κ)) := by
  simp only [VG.Proof.MlDsa.X86.Sign.w1Enc, w1Encode, List.flatMap_map]

/-- The commitment of iteration `t`. -/
theorem commit_piece {P : Prims} (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t : Nat) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.CM p t 0) (VG.Proof.MlDsa.X86.Sign.CC p t) (commit P p) := by
  have hw := ps.hw1
  have hc := ps.hcLen
  refine Piece.seq (B := VG.Proof.MlDsa.X86.Sign.CM p t p.ℓ) ?_ ?_
  · have := VG.Proof.MlDsa.X86.Sign.seqR_piece (p := p) (I := VG.Proof.MlDsa.X86.Sign.CM p t) 0 p.ℓ fun r _ hr => VG.Proof.MlDsa.X86.Sign.maskR_piece F ps t r (by omega)
    simpa using this
  refine Piece.seq (B := VG.Proof.MlDsa.X86.Sign.CW p t p.k) ?_ ?_
  · have := VG.Proof.MlDsa.X86.Sign.seqR_piece (p := p) (I := VG.Proof.MlDsa.X86.Sign.CW p t) 0 p.k fun i _ hi => VG.Proof.MlDsa.X86.Sign.rowW_piece F ps t i (by omega)
    simp only [Nat.zero_add] at this
    exact this.mono (fun _ _ _ h => ⟨h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩) fun _ _ _ h => h
  refine Piece.seq (B := VG.Proof.MlDsa.X86.Sign.CH p t p.k) ?_ ?_
  · have := VG.Proof.MlDsa.X86.Sign.seqR_piece (p := p) (I := VG.Proof.MlDsa.X86.Sign.CH p t) 0 p.k fun i _ hi => VG.Proof.MlDsa.X86.Sign.w1R_piece F ps t i (by omega)
    simp only [Nat.zero_add] at this
    exact this.mono (fun _ _ _ h => ⟨h, rfl⟩) fun _ _ _ h => h
  refine VG.Proof.MlDsa.X86.Sign.hash2_piece' 136 0x1f bMu (sc oW1 (p.k * w1Len p)) (sc oCT (cLen p)) (by decide) (by ofs) (by decide)
    (by show p.k * w1Len p < 2 ^ 32; omega) (by show cLen p < 2 ^ 32; omega) (fun _ _ _ h => h.cw.cm.it.kd.ctx)
    fun s₀ s s' hp h c' fr hb => ⟨h.cw.keep hp ps (Nat.le_refl _) c' (by decide) fr (by ofs), ?_⟩
  have e : BitVec.setWidth 8 (31#32) = Spec.Sha3.shakeSuffix := by decide
  have hw1 : bytesAt s.mem (Buf.addr s₀ (sc oW1 (p.k * w1Len p))) (p.k * w1Len p) = VG.Proof.MlDsa.X86.Sign.w1Enc p s₀ (p.ℓ * t) p.k := by
    rw [Nat.mul_comm]; exact h.w1
  simp only [sc, bMu] at hb hw1 ⊢
  rw [hb, hw1, h.cw.cm.it.kd.ctx.roBytes hp (b := bMu) (by ofs) rfl, e, VG.Proof.MlDsa.X86.Sign.w1Enc_eq, VG.Proof.MlDsa.X86.Sign.CTv, ctF,
    VG.Proof.MlDsa.Sample.H_eq]

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Run`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): what two related runs agree on

Whether every entry of `Â` was sampled (`Good`), and the number of iterations
of the loop (`NI`: the number the implementation's `SampleInBall` and the
checks make, or 1 if `Â` was not sampled), are the same in two runs related by
`SPub`; and at an iteration both reach (`t < NI`), so are `c̃`, whether
`SampleInBall` succeeded, whether the checks passed, and then the hint.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

section
variable (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P)

/-- Every entry of `Â` was sampled. -/
abbrev Good (s₀ : State) : Prop := VG.Proof.MlDsa.X86.Sign.okE p F.rejF s₀ (p.k * p.ℓ) = true

/-- The number of iterations of the loop. -/
def NI (s₀ : State) : Nat := if VG.Proof.MlDsa.X86.Sign.Good p F s₀ then itV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) F.ballF else 1

/-- The inputs, on entry. -/
abbrev sk₀ (s₀ : State) : List Byte := VG.Proof.MlDsa.X86.Sign.skOf p s₀

end

theorem NI_pos (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (s₀ : State) : 0 < VG.Proof.MlDsa.X86.Sign.NI p F s₀ := by
  unfold VG.Proof.MlDsa.X86.Sign.NI; split
  · exact nIt_pos _ (by decide)
  · decide

theorem NI_le (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (s₀ : State) : VG.Proof.MlDsa.X86.Sign.NI p F s₀ ≤ 814 := by
  unfold VG.Proof.MlDsa.X86.Sign.NI; split
  · exact nIt_le _ _
  · decide

theorem NI_good {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {s₀ : State} (h : VG.Proof.MlDsa.X86.Sign.Good p F s₀) :
    VG.Proof.MlDsa.X86.Sign.NI p F s₀ = itV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) F.ballF := by
  unfold VG.Proof.MlDsa.X86.Sign.NI; rw [VG.Proof.MlDsa.Sign.ifp h]

theorem seedE_eq {s₀ s₀' : State} (ps : VG.Proof.MlDsa.X86.Sign.PS p) (hq : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') (e : Nat) : VG.Proof.MlDsa.X86.Sign.seedE p s₀ e = VG.Proof.MlDsa.X86.Sign.seedE p s₀' e := by
  show aSeed (VG.Proof.MlDsa.X86.Sign.rhoS p s₀) _ _ = aSeed (VG.Proof.MlDsa.X86.Sign.rhoS p s₀') _ _; rw [VG.Proof.MlDsa.X86.Sign.rhoS_eq ps hq]

theorem okE_eq {F : List Byte → Bool} {s₀ s₀' : State} (ps : VG.Proof.MlDsa.X86.Sign.PS p) (hq : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') (e : Nat) :
    VG.Proof.MlDsa.X86.Sign.okE p F s₀ e = VG.Proof.MlDsa.X86.Sign.okE p F s₀' e := by
  simp only [VG.Proof.MlDsa.X86.Sign.okE, VG.Proof.MlDsa.X86.Sign.seedE_eq ps hq]

theorem skOf_len (ps : VG.Proof.MlDsa.X86.Sign.PS p) (s₀ : State) : 32 ≤ (VG.Proof.MlDsa.X86.Sign.skOf p s₀).length := by
  rw [VG.Proof.MlKem.bytesAt_length]; exact VG.Proof.MlDsa.X86.Sign.skLen_ge ps

/-- `ExpandA` succeeds within `maxBounds` once every entry was sampled. -/
theorem expandA_good {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {s₀ : State} (h : VG.Proof.MlDsa.X86.Sign.Good p F s₀) :
    expandA p maxBounds (rhoV (VG.Proof.MlDsa.X86.Sign.skOf p s₀)) = some (amat p (Av (VG.Proof.MlDsa.X86.Sign.skOf p s₀))) := by
  refine VG.Proof.MlDsa.Sign.expandA_some fun i hi j hj => ?_
  have hl : 0 < p.ℓ := by omega
  have he := VG.Proof.MlDsa.X86.Sign.okE_lt h (VG.Proof.MlDsa.X86.Sign.aIdx hi hj)
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [VG.Proof.MlDsa.X86.Sign.seedE, e1, e2] at he
  exact F.rejMax _ he

theorem leakV_eq {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {s₀ s₀' : State} (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.Good p F s₀) (h' : VG.Proof.MlDsa.X86.Sign.Good p F s₀')
    (hq : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') :
    leakV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) = leakV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀') (VG.Proof.MlDsa.X86.Sign.muOf s₀') (VG.Proof.MlDsa.X86.Sign.rndOf s₀') :=
  leakV_of_leak (VG.Proof.MlDsa.X86.Sign.skOf_len ps s₀) (VG.Proof.MlDsa.X86.Sign.skOf_len ps s₀') (VG.Proof.MlDsa.X86.Sign.expandA_good h) (VG.Proof.MlDsa.X86.Sign.expandA_good h') hq.2

theorem good_iff {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {s₀ s₀' : State} (ps : VG.Proof.MlDsa.X86.Sign.PS p) (hq : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') : VG.Proof.MlDsa.X86.Sign.Good p F s₀ ↔ VG.Proof.MlDsa.X86.Sign.Good p F s₀' := by
  simp only [VG.Proof.MlDsa.X86.Sign.Good, VG.Proof.MlDsa.X86.Sign.okE_eq ps hq]

theorem NI_eq {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {s₀ s₀' : State} (ps : VG.Proof.MlDsa.X86.Sign.PS p) (hq : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') : VG.Proof.MlDsa.X86.Sign.NI p F s₀ = VG.Proof.MlDsa.X86.Sign.NI p F s₀' := by
  by_cases h : VG.Proof.MlDsa.X86.Sign.Good p F s₀
  · have h' := (VG.Proof.MlDsa.X86.Sign.good_iff ps hq).mp h
    rw [VG.Proof.MlDsa.X86.Sign.NI_good h, VG.Proof.MlDsa.X86.Sign.NI_good h']
    exact itV_eq ps.hok F.ballMax (VG.Proof.MlDsa.X86.Sign.leakV_eq ps h h' hq)
  · have h' : ¬ VG.Proof.MlDsa.X86.Sign.Good p F s₀' := fun h' => h ((VG.Proof.MlDsa.X86.Sign.good_iff ps hq).mpr h')
    unfold VG.Proof.MlDsa.X86.Sign.NI; rw [VG.Proof.MlDsa.Sign.ifn h, VG.Proof.MlDsa.Sign.ifn h']

/-- Iteration `t` is run. -/
def Run (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (t : Nat) (s₀ : State) : Prop := VG.Proof.MlDsa.X86.Sign.Good p F s₀ ∧ t < VG.Proof.MlDsa.X86.Sign.NI p F s₀

instance {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {t : Nat} {s₀ : State} : Decidable (VG.Proof.MlDsa.X86.Sign.Run p F t s₀) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Run.cont {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {t : Nat} {s₀ : State} (h : VG.Proof.MlDsa.X86.Sign.Run p F t s₀) :
    ∀ j < t, contV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) F.ballF j = true := by
  have := h.2; rw [VG.Proof.MlDsa.X86.Sign.NI_good h.1] at this
  exact nIt_before _ this

theorem Run.lt {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {t : Nat} {s₀ : State} (h : VG.Proof.MlDsa.X86.Sign.Run p F t s₀) : t < 814 :=
  Nat.lt_of_lt_of_le h.2 (VG.Proof.MlDsa.X86.Sign.NI_le F s₀)

theorem run_iff {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : VG.Proof.MlDsa.X86.Sign.PS p) (hq : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') :
    VG.Proof.MlDsa.X86.Sign.Run p F t s₀ ↔ VG.Proof.MlDsa.X86.Sign.Run p F t s₀' := by
  simp only [VG.Proof.MlDsa.X86.Sign.Run, VG.Proof.MlDsa.X86.Sign.good_iff ps hq, VG.Proof.MlDsa.X86.Sign.NI_eq ps hq]

/-- At an iteration both runs reach: `c̃`, the success of `SampleInBall`,
the outcome of the checks, and the hint. -/
theorem run_at {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : VG.Proof.MlDsa.X86.Sign.PS p) (hq : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') (h : VG.Proof.MlDsa.X86.Sign.Run p F t s₀) :
    VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t) = VG.Proof.MlDsa.X86.Sign.CTv p s₀' (p.ℓ * t) ∧
      (F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = true →
        (passV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) (p.ℓ * t) ↔ passV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀') (VG.Proof.MlDsa.X86.Sign.muOf s₀') (VG.Proof.MlDsa.X86.Sign.rndOf s₀') (p.ℓ * t)) ∧
        (passV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) (p.ℓ * t) →
          hbitsV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) (p.ℓ * t) = hbitsV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀') (VG.Proof.MlDsa.X86.Sign.muOf s₀') (VG.Proof.MlDsa.X86.Sign.rndOf s₀') (p.ℓ * t))) :=
  leak_at ps.hok F.ballMax (VG.Proof.MlDsa.X86.Sign.leakV_eq ps h.1 ((VG.Proof.MlDsa.X86.Sign.good_iff ps hq).mp h.1) hq) (by show t < 1000; have := h.lt; omega) h.cont

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseK`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the checks of an iteration

Once `SampleInBall` succeeded (`ballCall_piece`), the checks (`CS`: what they
keep, with `y`, `w`, the hint, `OK` and `ONES` as far as they got) compute `z`
in place of `y` (`zR_piece`), `w - cs₂` in place of `w` and the norm of its
`LowBits` (`r0R_piece`), and `ct₀`, `w - cs₂ + ct₀` and the hint (`hR_piece`);
`OK` is then 1 exactly when the checks pass (`onesOk_piece`, `pass_iff`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_shr)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

section
variable (p : Params)

/-- `c`, and the values of the checks, of the iteration with counter `κ`. -/
abbrev Cv (s₀ : State) (κ : Nat) : IPoly := cV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) κ
abbrev Zv (s₀ : State) (κ r : Nat) : VG.Spec.MlDsa.Poly := zF p (VG.Proof.MlDsa.X86.Sign.S1 p s₀) (VG.Proof.MlDsa.X86.Sign.rppS p s₀) κ (VG.Proof.MlDsa.X86.Sign.Cv p s₀ κ) r
abbrev W'v (s₀ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := w'F p (VG.Proof.MlDsa.X86.Sign.Am p s₀) (VG.Proof.MlDsa.X86.Sign.S2 p s₀) (VG.Proof.MlDsa.X86.Sign.rppS p s₀) κ (VG.Proof.MlDsa.X86.Sign.Cv p s₀ κ) i
abbrev R0v (s₀ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := r0F p (VG.Proof.MlDsa.X86.Sign.Am p s₀) (VG.Proof.MlDsa.X86.Sign.S2 p s₀) (VG.Proof.MlDsa.X86.Sign.rppS p s₀) κ (VG.Proof.MlDsa.X86.Sign.Cv p s₀ κ) i
abbrev CT0v (s₀ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := ct0F (VG.Proof.MlDsa.X86.Sign.T0 p s₀) (VG.Proof.MlDsa.X86.Sign.Cv p s₀ κ) i
abbrev W''v (s₀ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := w''F p (VG.Proof.MlDsa.X86.Sign.Am p s₀) (VG.Proof.MlDsa.X86.Sign.S2 p s₀) (VG.Proof.MlDsa.X86.Sign.T0 p s₀) (VG.Proof.MlDsa.X86.Sign.rppS p s₀) κ (VG.Proof.MlDsa.X86.Sign.Cv p s₀ κ) i
abbrev Hv (s₀ : State) (κ i : Nat) : Vector Bool n := hF p (VG.Proof.MlDsa.X86.Sign.Am p s₀) (VG.Proof.MlDsa.X86.Sign.S2 p s₀) (VG.Proof.MlDsa.X86.Sign.T0 p s₀) (VG.Proof.MlDsa.X86.Sign.rppS p s₀) κ (VG.Proof.MlDsa.X86.Sign.Cv p s₀ κ) i

/-- The checks of the first `r` polynomials. -/
def okZ (s₀ : State) (κ r : Nat) : Bool := (List.range r).all fun j => decide (normRq [VG.Proof.MlDsa.X86.Sign.Zv p s₀ κ j] < p.γ₁ - p.β)
def okR (s₀ : State) (κ i : Nat) : Bool := (List.range i).all fun j => decide (normRq [VG.Proof.MlDsa.X86.Sign.R0v p s₀ κ j] < p.γ₂ - p.β)
def okT (s₀ : State) (κ i : Nat) : Bool := (List.range i).all fun j => decide (normRq [VG.Proof.MlDsa.X86.Sign.CT0v p s₀ κ j] < p.γ₂)
/-- The number of 1s of the first `i` polynomials of the hint. -/
def onesS (s₀ : State) (κ i : Nat) : Nat := ((List.range i).map fun j => hintOnes [VG.Proof.MlDsa.X86.Sign.Hv p s₀ κ j]).sum

end

theorem all_range_succ {f : Nat → Bool} {r : Nat} :
    (List.range (r + 1)).all f = ((List.range r).all f && f r) := by
  simp only [List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem all_range_iff {f : Nat → Prop} [DecidablePred f] {r : Nat} :
    (List.range r).all (fun j => decide (f j)) = true ↔ ∀ j < r, f j := by
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]

/-- The checks pass exactly when `OK` ends up 1. -/
theorem pass_iff {s₀ : State} {κ : Nat} :
    passV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) κ ↔
      (VG.Proof.MlDsa.X86.Sign.okZ p s₀ κ p.ℓ && VG.Proof.MlDsa.X86.Sign.okR p s₀ κ p.k && VG.Proof.MlDsa.X86.Sign.okT p s₀ κ p.k && decide (VG.Proof.MlDsa.X86.Sign.onesS p s₀ κ p.k ≤ p.ω)) = true := by
  simp only [Bool.and_eq_true, VG.Proof.MlDsa.X86.Sign.okZ, VG.Proof.MlDsa.X86.Sign.okR, VG.Proof.MlDsa.X86.Sign.okT, VG.Proof.MlDsa.X86.Sign.all_range_iff, VG.Proof.MlDsa.X86.Sign.onesS, passV, passF, and_assoc]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, decide_eq_true d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, of_decide_eq_true d⟩⟩

/-! ## The hint -/

/-- The first `nh` polynomials of the hint, in the slots from 5. -/
def HF (s₀ : State) (m : Mem) (nh : Nat) (f : Nat → Vector Bool n) : Prop :=
  ∀ j < nh, HintIs m (Buf.addr s₀ (pS (5 + j))) 1 [f j]

theorem hintIs_congr {m m' : Mem} {a : Addr} {h : Vector Bool n}
    (e : ∀ x < 1024, m' (a + BitVec.ofNat 64 x) = m (a + BitVec.ofNat 64 x)) (hh : HintIs m a 1 [h]) :
    HintIs m' a 1 [h] := by
  refine ⟨hh.1, fun i hi j hj => ?_⟩
  have : coeffAt m' a (256 * i + j) = coeffAt m a (256 * i + j) := by
    unfold coeffAt
    refine Mem.readW_congr fun t ht => ?_
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact e _ (by have : n = 256 := rfl; omega)
  rw [this]; exact hh.2 i hi j hj

theorem HF.keep {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {nh : Nat} (hn : 5 + nh ≤ VG.Proof.MlDsa.X86.Sign.nS p)
    (h : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP 5) (VG.Impl.MlDsa.X86.Sign.oP (5 + nh)) c) {f : Nat → Vector Bool n} (hf : VG.Proof.MlDsa.X86.Sign.HF s₀ m nh f) : VG.Proof.MlDsa.X86.Sign.HF s₀ m' nh f :=
  fun j hj => VG.Proof.MlDsa.X86.Sign.hintIs_congr (VG.Proof.MlKem.X86.Top.keep hp (N := N) (by show N + 16 ≤ 96; omega)
    (VG.Proof.MlDsa.X86.Sign.apart_of (VG.Proof.MlDsa.X86.Sign.slot_ok' ps (by omega)) rfl fun c hc => by
      obtain ⟨h₁, h₂⟩ := h c hc
      exact ⟨h₁, fun e => by simp only [VG.Impl.MlDsa.X86.Sign.oP] at h₂ ⊢; have := h₂ e; omega⟩) fr) (hf j hj)

theorem HF.snoc {s₀ : State} {m : Mem} {nh : Nat} {f : Nat → Vector Bool n} (h : VG.Proof.MlDsa.X86.Sign.HF s₀ m nh f)
    (h' : HintIs m (Buf.addr s₀ (pS (5 + nh))) 1 [f nh]) : VG.Proof.MlDsa.X86.Sign.HF s₀ m (nh + 1) f := fun j hj => by
  by_cases e : j < nh
  · exact h j e
  · rw [show j = nh by omega]; exact h'

/-- Slot `r` of a family changed, the others kept. -/
theorem Fam.upd {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {b n r : Nat} (hb : b + n ≤ VG.Proof.MlDsa.X86.Sign.nS p) (hr : r < n)
    (h : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP b) (VG.Impl.MlDsa.X86.Sign.oP (b + r)) c ∧ VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP (b + r + 1)) (VG.Impl.MlDsa.X86.Sign.oP (b + n)) c) {f g : Nat → VG.Spec.MlDsa.Poly}
    (hf : VG.Proof.MlDsa.X86.Sign.Fam s₀ m b n f) (hv : PolyIs m' (Buf.addr s₀ (pS (b + r))) (g r)) (hg : ∀ j < n, j ≠ r → g j = f j) :
    VG.Proof.MlDsa.X86.Sign.Fam s₀ m' b n g := fun j hj => by
  by_cases e : j = r
  · subst e; exact hv
  · rw [hg j hj e]
    exact VG.Proof.MlDsa.X86.Sign.keepP hp ps hN fr (by omega) (fun c hc => by
      obtain ⟨⟨h₁, h₂⟩, -, h₃⟩ := h c hc
      exact ⟨h₁, fun ea => by
        have := h₂ ea; have := h₃ ea; simp only [VG.Impl.MlDsa.X86.Sign.oP] at *
        rcases (by omega : j < r ∨ r < j) with hj' | hj' <;> omega⟩) (hf j hj)

/-! ## The state of the checks -/

/-- The checks of iteration `t`, with `y`, `w`, the first `nh` polynomials of
the hint, `OK` and `ONES` as `fY`, `fW`, `okb` and `ones` say. -/
structure CS (p : Params) (t : Nat) (fY fW : State → Nat → VG.Spec.MlDsa.Poly) (nh : Nat) (okb : State → Bool)
    (ones : State → Nat) (s₀ s : State) : Prop where
  it : VG.Proof.MlDsa.X86.Sign.IT p t s₀ s
  ct : bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)
  c : PolyIs s.mem (Buf.addr s₀ cP) (chF (VG.Proof.MlDsa.X86.Sign.Cv p s₀ (p.ℓ * t)))
  fy : VG.Proof.MlDsa.X86.Sign.Fam s₀ s.mem (VG.Proof.MlDsa.X86.Sign.yB p) p.ℓ (fY s₀)
  fw : VG.Proof.MlDsa.X86.Sign.Fam s₀ s.mem (VG.Proof.MlDsa.X86.Sign.wB p) p.k (fW s₀)
  fh : VG.Proof.MlDsa.X86.Sign.HF s₀ s.mem nh (VG.Proof.MlDsa.X86.Sign.Hv p s₀ (p.ℓ * t))
  ok : VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = if okb s₀ then 1 else 0
  ones : VG.Proof.MlDsa.X86.Sign.scw s₀ s oONES = BitVec.ofNat 32 (ones s₀)
  nh : nh ≤ p.k

section
variable {t nh : Nat} {fY fW : State → Nat → VG.Spec.MlDsa.Poly} {okb : State → Bool} {ones : State → Nat}
  {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s) (c' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s')
  {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
include hp ps h c' hN fr

omit c' in
theorem CS.ct_keep (hb : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.Out p oCT (oCT + 64) c) :
    bytesAt s'.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t) := by
  have := ps.hcLen
  rw [VG.Proof.MlDsa.X86.Sign.keepB hp hN fr (by ofs) fun c hc => ⟨(hb c hc).1, fun e => by
    have := (hb c hc).2 e; simp only [oCT] at this ⊢; omega⟩, h.ct]

theorem CS.keep (hb : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.OutC p nh c) : VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s' := by
  have := h.nh
  exact ⟨h.it.keep hp ps c' hN fr fun c hc => (hb c hc).1, h.ct_keep hp ps hN fr fun c hc => (hb c hc).2.2.1,
    VG.Proof.MlDsa.X86.Sign.keepP hp ps hN fr (j := 0) (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (fun c hc => (hb c hc).2.1) h.c,
    h.fy.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) fun c hc => ⟨(hb c hc).2.2.2.1.1, fun e => by
      have := (hb c hc).2.2.2.1.2 e; simp only [VG.Impl.MlDsa.X86.Sign.oP, VG.Proof.MlDsa.X86.Sign.yB, VG.Proof.MlDsa.X86.Sign.wB] at this ⊢; omega⟩,
    h.fw.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.wB]; omega) fun c hc => ⟨(hb c hc).2.2.2.1.1, fun e => by
      have := (hb c hc).2.2.2.1.2 e; simp only [VG.Impl.MlDsa.X86.Sign.oP, VG.Proof.MlDsa.X86.Sign.yB, VG.Proof.MlDsa.X86.Sign.wB] at this ⊢; omega⟩,
    h.fh.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) fun c hc => (hb c hc).2.2.2.2.1,
    by rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp hN fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2.2.2.2.2.1]; exact h.ok,
    by rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp hN fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2.2.2.2.2.2]; exact h.ones,
    h.nh⟩

end

/-! ## `SampleInBall` -/

theorem ball_val {τ : Nat} {x : List Byte} {r : BitVec 32} {out : VG.Spec.MlDsa.Poly}
    (h : Outcome (fun b => (VG.Spec.MlDsa.sampleInBall τ b.ball x).map toRq) r out) (h1 : r = 1)
    (hm : (VG.Spec.MlDsa.sampleInBall τ maxBounds.ball x).isSome) :
    out = toRq ((VG.Spec.MlDsa.sampleInBall τ maxBounds.ball x).getD (Vector.replicate n 0)) := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
    have e1 := sampleInBall_mono (Nat.le_max_left b.ball maxBounds.ball) hc
    have e2 := sampleInBall_mono (Nat.le_max_right b.ball maxBounds.ball) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

/-- After `SampleInBall` in iteration `t`. -/
structure IB (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  cc : VG.Proof.MlDsa.X86.Sign.CC p t s₀ s
  run : VG.Proof.MlDsa.X86.Sign.Run p F t s₀
  eax : s.gpr .eax = if F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) then 1 else 0
  yes : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = true → PolyIs s.mem (Buf.addr s₀ cP) (toRq (VG.Proof.MlDsa.X86.Sign.Cv p s₀ (p.ℓ * t)))
  no : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = false → VG.Spec.MlDsa.sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = none

theorem CC.keep {t : Nat} {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.CC p t s₀ s)
    (c' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s') {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, (VG.Proof.MlDsa.X86.Sign.OutI p c ∧ VG.Proof.MlDsa.X86.Sign.Out p (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.yB p)) (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + p.k)) c) ∧ VG.Proof.MlDsa.X86.Sign.Out p oCT (oCT + 64) c) : VG.Proof.MlDsa.X86.Sign.CC p t s₀ s' := by
  have := ps.hcLen
  exact ⟨h.cw.keep hp ps (Nat.le_refl _) c' hN fr fun c hc => (hb c hc).1, by
    rw [VG.Proof.MlDsa.X86.Sign.keepB hp hN fr (by ofs) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [oCT] at this ⊢; omega⟩, h.ct]⟩

/-- `c = SampleInBall(c̃)` to `ĉ`'s slot. -/
theorem ballCall_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t : Nat) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlDsa.X86.Sign.CC p t s₀ s ∧ VG.Proof.MlDsa.X86.Sign.Run p F t s₀) (VG.Proof.MlDsa.X86.Sign.IB p F t) (ballAt P (cLen p) p.τ cP) := by
  have := ps.hcLen
  refine VG.Proof.MlDsa.X86.Sign.ball_piece F.ball (F.ok _ (by simp)) (cLen p) p.τ ps.hball SC oCT SC (VG.Impl.MlDsa.X86.Sign.oP 0) SC oPS (by ofs)
    (fun _ _ _ h => h.1.cw.cm.it.kd.ctx) (fun s₀ s₀' s s' hp hp' hq h h' => ?_)
    fun s₀ s s' hp h c' fr heax hred hout => ?_
  · rw [h.1.ct, h'.1.ct]; exact (VG.Proof.MlDsa.X86.Sign.run_at ps hq h.2).1
  · rw [h.1.ct] at heax hout
    refine ⟨h.1.keep hp ps c' (by decide) fr (by ofs), h.2, heax, fun hy => ?_, fun hn => ?_⟩
    · rw [hy] at heax; simp only [↓reduceIte] at heax
      exact ⟨hred heax, VG.Proof.MlDsa.X86.Sign.ball_val hout heax (F.ballMax _ _ hy)⟩
    · rw [hn] at heax
      rcases hout with ⟨h1, _⟩ | ⟨_, h0⟩
      · rw [heax] at h1; cases h1
      · simpa using h0

/-- Whether `SampleInBall` succeeded, in a run that reaches iteration `t`. -/
def ballB (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (t : Nat) (s₀ : State) : Bool :=
  decide (VG.Proof.MlDsa.X86.Sign.Run p F t s₀) && F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t))

theorem ballB_eq {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : VG.Proof.MlDsa.X86.Sign.PS p) (hq : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') :
    VG.Proof.MlDsa.X86.Sign.ballB p F t s₀ = VG.Proof.MlDsa.X86.Sign.ballB p F t s₀' := by
  unfold VG.Proof.MlDsa.X86.Sign.ballB
  by_cases h : VG.Proof.MlDsa.X86.Sign.Run p F t s₀
  · rw [decide_eq_true h, decide_eq_true ((VG.Proof.MlDsa.X86.Sign.run_iff ps hq).mp h), (VG.Proof.MlDsa.X86.Sign.run_at ps hq h).1]
  · rw [decide_eq_false h, decide_eq_false fun h' => h ((VG.Proof.MlDsa.X86.Sign.run_iff ps hq).mpr h'), Bool.false_and, Bool.false_and]

theorem ballB_of {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {t : Nat} {s₀ : State} (h : VG.Proof.MlDsa.X86.Sign.Run p F t s₀) :
    VG.Proof.MlDsa.X86.Sign.ballB p F t s₀ = F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) := by
  simp only [VG.Proof.MlDsa.X86.Sign.ballB, decide_eq_true h, Bool.true_and]

/-- `ZF ← eax = 0`, after `SampleInBall`. -/
theorem ballTest_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (t : Nat) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.IB p F t) (fun s₀ s => ∃ s', VG.Proof.MlDsa.X86.Sign.IB p F t s₀ s' ∧ VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ s.mem = s'.mem ∧
      s.zf = some (!VG.Proof.MlDsa.X86.Sign.ballB p F t s₀)) (.block [.alu .test .eax (.reg .eax)]) := by
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.cc.cw.cm.it.kd.ctx) (fun s₀ s hp h => VG.Proof.MlDsa.X86.Sign.wp_test fun s₁ o₁ z₁ =>
    WP.block_nil_iff.mpr ⟨s, h, h.cc.cw.cm.it.kd.ctx.only o₁ (by simp) (by simp), o₁.mem, ?_⟩) rfl
  rw [z₁, h.eax, VG.Proof.MlDsa.X86.Sign.ballB_of h.run]
  cases F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) <;> rfl

/-! ## The start of the checks -/

/-- `y`, with `z` in place of its first `r` polynomials. -/
abbrev zY (p : Params) (t r : Nat) (s₀ : State) (j : Nat) : VG.Spec.MlDsa.Poly :=
  if j < r then VG.Proof.MlDsa.X86.Sign.Zv p s₀ (p.ℓ * t) j else VG.Proof.MlDsa.X86.Sign.Yv p s₀ (p.ℓ * t) j

/-- `w`, with `w - cs₂` in place of its first `i` polynomials. -/
abbrev rW (p : Params) (t i : Nat) (s₀ : State) (j : Nat) : VG.Spec.MlDsa.Poly :=
  if j < i then VG.Proof.MlDsa.X86.Sign.W'v p s₀ (p.ℓ * t) j else VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t) j

/-- `w - cs₂`, with `w - cs₂ + ct₀` in place of its first `i` polynomials. -/
abbrev hW (p : Params) (t i : Nat) (s₀ : State) (j : Nat) : VG.Spec.MlDsa.Poly :=
  if j < i then VG.Proof.MlDsa.X86.Sign.W''v p s₀ (p.ℓ * t) j else VG.Proof.MlDsa.X86.Sign.W'v p s₀ (p.ℓ * t) j

theorem zY_lt {t r j : Nat} {s₀ : State} (h : j < r) : VG.Proof.MlDsa.X86.Sign.zY p t r s₀ j = VG.Proof.MlDsa.X86.Sign.Zv p s₀ (p.ℓ * t) j := VG.Proof.MlDsa.Sign.ifp h _ _
theorem zY_ge {t r j : Nat} {s₀ : State} (h : ¬ j < r) : VG.Proof.MlDsa.X86.Sign.zY p t r s₀ j = VG.Proof.MlDsa.X86.Sign.Yv p s₀ (p.ℓ * t) j := VG.Proof.MlDsa.Sign.ifn h _ _
theorem rW_lt {t i j : Nat} {s₀ : State} (h : j < i) : VG.Proof.MlDsa.X86.Sign.rW p t i s₀ j = VG.Proof.MlDsa.X86.Sign.W'v p s₀ (p.ℓ * t) j := VG.Proof.MlDsa.Sign.ifp h _ _
theorem rW_ge {t i j : Nat} {s₀ : State} (h : ¬ j < i) : VG.Proof.MlDsa.X86.Sign.rW p t i s₀ j = VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t) j := VG.Proof.MlDsa.Sign.ifn h _ _
theorem hW_lt {t i j : Nat} {s₀ : State} (h : j < i) : VG.Proof.MlDsa.X86.Sign.hW p t i s₀ j = VG.Proof.MlDsa.X86.Sign.W''v p s₀ (p.ℓ * t) j := VG.Proof.MlDsa.Sign.ifp h _ _
theorem hW_ge {t i j : Nat} {s₀ : State} (h : ¬ j < i) : VG.Proof.MlDsa.X86.Sign.hW p t i s₀ j = VG.Proof.MlDsa.X86.Sign.W'v p s₀ (p.ℓ * t) j := VG.Proof.MlDsa.Sign.ifn h _ _

/-- The family whose first `r` values are `g` changed at `r`, for `r + 1`. -/
theorem upd_step {α : Type} {f g : Nat → α} {r j : Nat} (h : j ≠ r) :
    (if j < r + 1 then g j else f j) = if j < r then g j else f j := by
  by_cases e : j < r
  · rw [VG.Proof.MlDsa.Sign.ifp (by omega : j < r + 1), VG.Proof.MlDsa.Sign.ifp e]
  · rw [VG.Proof.MlDsa.Sign.ifn (by omega : ¬ j < r + 1), VG.Proof.MlDsa.Sign.ifn e]

/-- What the checks start from. -/
structure KP (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  cc : VG.Proof.MlDsa.X86.Sign.CC p t s₀ s
  run : VG.Proof.MlDsa.X86.Sign.Run p F t s₀
  ball : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = true

theorem CC.ofMem {t : Nat} {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.CC p t s₀ s')
    (c : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) (hm : s.mem = s'.mem) : VG.Proof.MlDsa.X86.Sign.CC p t s₀ s :=
  h.keep hp ps c (N := 0) (bs := []) (by decide) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- `OK ← 1` and `ONES ← 0`. -/
theorem checksInit_piece (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t : Nat) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlDsa.X86.Sign.CC p t s₀ s ∧ PolyIs s.mem (Buf.addr s₀ cP) (chF (VG.Proof.MlDsa.X86.Sign.Cv p s₀ (p.ℓ * t))))
      (VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t 0) (fun s₀ => VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t)) 0 (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) 0) (fun _ => 0))
      (.block (st32 oOK 1 ++ st32 oONES 0)) := by
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.1.cw.cm.it.kd.ctx) (fun s₀ s hp h => ?_) rfl
  refine VG.Proof.MlDsa.X86.Sign.wp_st32 hp h.1.cw.cm.it.kd.ctx (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) 1 fun s₁ c₁ f₁ v₁ => ?_
  rw [← List.append_nil (st32 oONES 0)]
  refine VG.Proof.MlDsa.X86.Sign.wp_st32 hp c₁ (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) 0 fun s₂ c₂ f₂ v₂ => WP.block_nil_iff.mpr ?_
  have g₁ := (h.1.keep hp ps c₁ (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) f₁) (by ofs))
  have g₂ := (g₁.keep hp ps c₂ (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) f₂) (by ofs))
  have hc := VG.Proof.MlDsa.X86.Sign.keepP hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) f₁) (j := 0) (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs) h.2
  have hc' := VG.Proof.MlDsa.X86.Sign.keepP hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) f₂) (j := 0) (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs) hc
  refine ⟨g₂.cw.cm.it, g₂.ct, hc', g₂.cw.cm.fy.congr fun j hj => by simp, g₂.cw.fw, fun j hj => absurd hj (Nat.not_lt_zero _),
    ?_, v₂, Nat.zero_le _⟩
  rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) f₂) (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)]
  exact v₁

/-! ## Norms -/

/-- `OK ← OK ∧ b`, with `eax = b`. -/
theorem CS.setOK {t nh : Nat} {fY fW : State → Nat → VG.Spec.MlDsa.Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s) (c' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s')
    (fr : Frame (FR s₀ [sc oOK 4] 0) s.mem s'.mem) (b : State → Bool)
    (v : VG.Proof.MlDsa.X86.Sign.scw s₀ s' oOK = VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK &&& s.gpr .eax) (he : s.gpr .eax = if b s₀ then 1 else 0) :
    VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh (fun s₀ => okb s₀ && b s₀) ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (by ofs),
    h.ct_keep hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (by ofs),
    VG.Proof.MlDsa.X86.Sign.keepP hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (j := 0) (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs) h.c,
    h.fy.keep hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) (by ofs),
    h.fw.keep hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.wB]; omega) (by ofs),
    h.fh.keep hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs),
    by rw [v, h.ok, he, VG.Proof.MlDsa.X86.Sign.and01], ?_, h.nh⟩
  rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)]
  exact h.ones

/-- `OK ← OK ∧ ‖f‖∞ < bnd`, for the polynomial `v` in slot `j`, which stays. -/
theorem normAnd_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {t nh : Nat} {fY fW : State → Nat → VG.Spec.MlDsa.Poly} {okb : State → Bool}
    {ones : State → Nat} (j : Nat) (hj : j < VG.Proof.MlDsa.X86.Sign.nS p) (bnd : Nat) (hb : bnd < 2 ^ 32) (v : State → VG.Spec.MlDsa.Poly) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀))
      (fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh (fun s₀ => okb s₀ && decide (normRq [v s₀] < bnd)) ones s₀ s ∧
        PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀)) (normAt P (pS j) bnd) := by
  refine Piece.seq (B := fun s₀ s => (VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀)) ∧
      s.gpr .eax = if normRq [v s₀] < bnd then 1 else 0)
    (VG.Proof.MlDsa.X86.Sign.norm_piece F.normLt (F.ok _ (by simp)) bnd hb SC (VG.Impl.MlDsa.X86.Sign.oP j) (VG.Proof.MlDsa.X86.Sign.slot_ok' ps hj) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr he => ⟨⟨h.1.keep hp ps c' (by decide) fr (by simp),
        VG.Proof.MlDsa.X86.Sign.keepP hp ps (by decide) fr hj (by simp) h.2⟩, by rw [he, h.2.2]⟩) ?_
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.1.1.it.kd.ctx) (fun s₀ s hp h => VG.Proof.MlDsa.X86.Sign.wp_andOK hp h.1.1.it.kd.ctx ps
    fun s' c' fr v' => ⟨h.1.1.setOK hp ps c' fr (fun s₀ => decide (normRq [v s₀] < bnd)) v' ?_,
      VG.Proof.MlDsa.X86.Sign.keepP hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) hj (by ofs) h.1.2⟩) rfl
  rw [h.2]; by_cases e : normRq [v s₀] < bnd <;> simp [e]

theorem CS.congr {t nh : Nat} {fY fY' fW fW' : State → Nat → VG.Spec.MlDsa.Poly} {okb okb' : State → Bool} {ones : State → Nat}
    {s₀ s : State} (h : VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s) (e₁ : ∀ j < p.ℓ, fY s₀ j = fY' s₀ j)
    (e₂ : ∀ j < p.k, fW s₀ j = fW' s₀ j) (e₃ : okb s₀ = okb' s₀) : VG.Proof.MlDsa.X86.Sign.CS p t fY' fW' nh okb' ones s₀ s :=
  { h with fy := h.fy.congr e₁, fw := h.fw.congr e₂, ok := by rw [h.ok, e₃] }

/-- Slot `r` of `y` changed. -/
theorem CS.updY {t nh r : Nat} {fY fW : State → Nat → VG.Spec.MlDsa.Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s) (c' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s')
    (hr : r < p.ℓ) (fr : Frame (FR s₀ [pS (VG.Proof.MlDsa.X86.Sign.yB p + r)] 80) s.mem s'.mem) {fY' : State → Nat → VG.Spec.MlDsa.Poly}
    (hv : PolyIs s'.mem (Buf.addr s₀ (pS (VG.Proof.MlDsa.X86.Sign.yB p + r))) (fY' s₀ r)) (hg : ∀ j < p.ℓ, j ≠ r → fY' s₀ j = fY s₀ j) :
    VG.Proof.MlDsa.X86.Sign.CS p t fY' fW nh okb ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (by decide) fr (by ofs), h.ct_keep hp ps (by decide) fr (by ofs),
    VG.Proof.MlDsa.X86.Sign.keepP hp ps (by decide) fr (j := 0) (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs) h.c,
    h.fy.upd hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) hr (by ofs) hv hg,
    h.fw.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.wB]; omega) (by ofs),
    h.fh.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs),
    by rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ok,
    by rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ones, h.nh⟩

/-- Slot `i` of `w` changed. -/
theorem CS.updW {t nh i : Nat} {fY fW : State → Nat → VG.Spec.MlDsa.Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s) (c' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s')
    (hi : i < p.k) (fr : Frame (FR s₀ [pS (VG.Proof.MlDsa.X86.Sign.wB p + i)] 80) s.mem s'.mem) {fW' : State → Nat → VG.Spec.MlDsa.Poly}
    (hv : PolyIs s'.mem (Buf.addr s₀ (pS (VG.Proof.MlDsa.X86.Sign.wB p + i))) (fW' s₀ i)) (hg : ∀ j < p.k, j ≠ i → fW' s₀ j = fW s₀ j) :
    VG.Proof.MlDsa.X86.Sign.CS p t fY fW' nh okb ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (by decide) fr (by ofs), h.ct_keep hp ps (by decide) fr (by ofs),
    VG.Proof.MlDsa.X86.Sign.keepP hp ps (by decide) fr (j := 0) (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs) h.c,
    h.fy.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) (by ofs),
    h.fw.upd hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.wB]; omega) hi (by ofs) hv hg,
    h.fh.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs),
    by rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ok,
    by rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ones, h.nh⟩

/-! ## `z` -/

/-- `z[r] = y[r] + NTT⁻¹(ĉ ŝ₁[r])` in place of `y[r]`, and its norm. -/
theorem zR_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t r : Nat) (hr : r < p.ℓ) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t r) (fun s₀ => VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t)) 0 (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) r) (fun _ => 0))
      (VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t (r + 1)) (fun s₀ => VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t)) 0 (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) (r + 1)) (fun _ => 0))
      (zR P p r) := by
  have hj : VG.Proof.MlDsa.X86.Sign.s1B p + r < VG.Proof.MlDsa.X86.Sign.nS p := by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.s1B]; omega
  have hy : VG.Proof.MlDsa.X86.Sign.yB p + r < VG.Proof.MlDsa.X86.Sign.nS p := by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega
  have hβ := ps.hβ
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t r) (fun s₀ => VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) r) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (multiplyNTT (chF (VG.Proof.MlDsa.X86.Sign.Cv p s₀ (p.ℓ * t))) (VG.Proof.MlDsa.X86.Sign.S1 p s₀ r)))
    (VG.Proof.MlDsa.X86.Sign.mul_piece F.mul (F.ok _ (by simp)) SC (VG.Impl.MlDsa.X86.Sign.oP 1) SC (VG.Impl.MlDsa.X86.Sign.oP 0) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.s1B p + r)) (by ofs)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (VG.Proof.MlDsa.X86.Sign.fam_at h.it.kd.dk.f1 hr).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofs), by
        rw [h.c.2, (VG.Proof.MlDsa.X86.Sign.fam_at h.it.kd.dk.f1 hr).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t r) (fun s₀ => VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) r) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (VG.Spec.MlDsa.nttInv (multiplyNTT (chF (VG.Proof.MlDsa.X86.Sign.Cv p s₀ (p.ℓ * t))) (VG.Proof.MlDsa.X86.Sign.S1 p s₀ r))))
    (VG.Proof.MlDsa.X86.Sign.inPlace_piece (t := VG.Spec.MlDsa.nttInv) F.invNtt (F.ok _ (by simp)) t1P rfl (by ofs) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofs), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t (r + 1)) (fun s₀ => VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) r) (fun _ => 0))
    (VG.Proof.MlDsa.X86.Sign.acc_piece (op := VG.Spec.MlDsa.add) F.add (F.ok _ (by simp)) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.yB p + r)) SC (VG.Impl.MlDsa.X86.Sign.oP 1) (by ofs)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, (VG.Proof.MlDsa.X86.Sign.fam_at h.1.fy hr).1, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => h.1.updY hp ps c' hr fr (by
        rw [(VG.Proof.MlDsa.X86.Sign.fam_at h.1.fy hr).2, h.2.2, VG.Proof.MlDsa.X86.Sign.zY_ge (Nat.lt_irrefl r)] at hq
        rw [VG.Proof.MlDsa.X86.Sign.zY_lt (Nat.lt_succ_self r)]; exact hq) fun j _ hjr => VG.Proof.MlDsa.X86.Sign.upd_step hjr) ?_
  refine (VG.Proof.MlDsa.X86.Sign.normAnd_piece F ps (VG.Proof.MlDsa.X86.Sign.yB p + r) hy (p.γ₁ - p.β) (by omega) (fun s₀ => VG.Proof.MlDsa.X86.Sign.Zv p s₀ (p.ℓ * t) r)).mono
    (fun s₀ s _ h => ⟨h, by have := VG.Proof.MlDsa.X86.Sign.fam_at h.fy hr; rwa [VG.Proof.MlDsa.X86.Sign.zY_lt (Nat.lt_succ_self r)] at this⟩)
    fun s₀ s _ h => h.1.congr (fun _ _ => rfl)
      (fun _ _ => rfl) (by simp only [VG.Proof.MlDsa.X86.Sign.okZ, VG.Proof.MlDsa.X86.Sign.all_range_succ])

/-! ## `r₀` -/

/-- `w[i] - NTT⁻¹(ĉ ŝ₂[i])` in place of `w[i]`, and the norm of its `LowBits`. -/
theorem r0R_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t i : Nat) (hi : i < p.k) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.rW p t i) 0 (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) p.ℓ && VG.Proof.MlDsa.X86.Sign.okR p s₀ (p.ℓ * t) i) (fun _ => 0))
      (VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.rW p t (i + 1)) 0 (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) p.ℓ && VG.Proof.MlDsa.X86.Sign.okR p s₀ (p.ℓ * t) (i + 1))
        (fun _ => 0)) (r0R P p i) := by
  have hj : VG.Proof.MlDsa.X86.Sign.s2B p + i < VG.Proof.MlDsa.X86.Sign.nS p := by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.s2B]; omega
  have hβ := ps.hβ
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.rW p t i) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) p.ℓ && VG.Proof.MlDsa.X86.Sign.okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (multiplyNTT (chF (VG.Proof.MlDsa.X86.Sign.Cv p s₀ (p.ℓ * t))) (VG.Proof.MlDsa.X86.Sign.S2 p s₀ i)))
    (VG.Proof.MlDsa.X86.Sign.mul_piece F.mul (F.ok _ (by simp)) SC (VG.Impl.MlDsa.X86.Sign.oP 1) SC (VG.Impl.MlDsa.X86.Sign.oP 0) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.s2B p + i)) (by ofs)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (VG.Proof.MlDsa.X86.Sign.fam_at h.it.kd.dk.f2 hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofs), by
        rw [h.c.2, (VG.Proof.MlDsa.X86.Sign.fam_at h.it.kd.dk.f2 hi).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.rW p t i) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) p.ℓ && VG.Proof.MlDsa.X86.Sign.okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (VG.Spec.MlDsa.nttInv (multiplyNTT (chF (VG.Proof.MlDsa.X86.Sign.Cv p s₀ (p.ℓ * t))) (VG.Proof.MlDsa.X86.Sign.S2 p s₀ i))))
    (VG.Proof.MlDsa.X86.Sign.inPlace_piece (t := VG.Spec.MlDsa.nttInv) F.invNtt (F.ok _ (by simp)) t1P rfl (by ofs) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofs), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.rW p t (i + 1)) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) p.ℓ && VG.Proof.MlDsa.X86.Sign.okR p s₀ (p.ℓ * t) i) (fun _ => 0))
    (VG.Proof.MlDsa.X86.Sign.acc_piece (op := VG.Spec.MlDsa.sub) F.sub (F.ok _ (by simp)) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + i)) SC (VG.Impl.MlDsa.X86.Sign.oP 1) (by ofs)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, (VG.Proof.MlDsa.X86.Sign.fam_at h.1.fw hi).1, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => h.1.updW hp ps c' hi fr (by
        rw [(VG.Proof.MlDsa.X86.Sign.fam_at h.1.fw hi).2, h.2.2, VG.Proof.MlDsa.X86.Sign.rW_ge (Nat.lt_irrefl i)] at hq
        rw [VG.Proof.MlDsa.X86.Sign.rW_lt (Nat.lt_succ_self i)]; exact hq) fun j _ hji => VG.Proof.MlDsa.X86.Sign.upd_step hji) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.rW p t (i + 1)) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) p.ℓ && VG.Proof.MlDsa.X86.Sign.okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t2P) (VG.Proof.MlDsa.X86.Sign.R0v p s₀ (p.ℓ * t) i))
    (VG.Proof.MlDsa.X86.Sign.lb_piece F.lowBits (F.ok _ (by simp)) p.γ₂ ps.hγ₂ SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + i)) SC (VG.Impl.MlDsa.X86.Sign.oP 2) (by ofs)
      (fun _ _ _ h => ⟨h.it.kd.ctx, (VG.Proof.MlDsa.X86.Sign.fam_at h.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofs), by
        rw [(VG.Proof.MlDsa.X86.Sign.fam_at h.fw hi).2, VG.Proof.MlDsa.X86.Sign.rW_lt (Nat.lt_succ_self i)] at hq; exact hq⟩) ?_
  refine (VG.Proof.MlDsa.X86.Sign.normAnd_piece F ps 2 (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (p.γ₂ - p.β) (by omega) (fun s₀ => VG.Proof.MlDsa.X86.Sign.R0v p s₀ (p.ℓ * t) i)).mono
    (fun s₀ s _ h => h) fun s₀ s _ h => h.1.congr (fun _ _ => rfl) (fun _ _ => rfl)
      (by simp only [VG.Proof.MlDsa.X86.Sign.okR, VG.Proof.MlDsa.X86.Sign.all_range_succ, Bool.and_assoc])

/-! ## `ct₀` and the hint -/

theorem zq_sub_add (a b : Zq) : a - (a + b) = -b := by
  apply Fin.ext
  have ha := a.isLt; have hb := b.isLt
  simp only [Fin.sub_def, Fin.add_def, Fin.neg_def, q] at *
  omega

theorem sub_add_neg (a b : VG.Spec.MlDsa.Poly) : VG.Spec.MlDsa.sub a (VG.Spec.MlDsa.add a b) = neg b := by
  apply Vector.ext
  intro j hj
  simp only [VG.Spec.MlDsa.sub, VG.Spec.MlDsa.add, neg, Vector.getElem_zipWith, Vector.getElem_map, VG.Proof.MlDsa.X86.Sign.zq_sub_add]

theorem hintOnes_le (h : Vector Bool n) : hintOnes [h] ≤ 256 := by
  rw [VG.Proof.MlDsa.Sign.hintOnes_single]
  exact Nat.le_trans (List.length_filter_le _ _) (by rw [Vector.length_toList])

theorem sum_range_succ (f : Nat → Nat) (i : Nat) :
    ((List.range (i + 1)).map f).sum = ((List.range i).map f).sum + f i := by
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero]

theorem onesS_succ {s₀ : State} {κ i : Nat} : VG.Proof.MlDsa.X86.Sign.onesS p s₀ κ (i + 1) = VG.Proof.MlDsa.X86.Sign.onesS p s₀ κ i + hintOnes [VG.Proof.MlDsa.X86.Sign.Hv p s₀ κ i] :=
  VG.Proof.MlDsa.X86.Sign.sum_range_succ _ i

theorem onesS_le {s₀ : State} {κ : Nat} : ∀ i, VG.Proof.MlDsa.X86.Sign.onesS p s₀ κ i ≤ 256 * i
  | 0 => by simp [VG.Proof.MlDsa.X86.Sign.onesS]
  | i + 1 => by rw [VG.Proof.MlDsa.X86.Sign.onesS_succ]; have := VG.Proof.MlDsa.X86.Sign.onesS_le (s₀ := s₀) (κ := κ) i; have := VG.Proof.MlDsa.X86.Sign.hintOnes_le (VG.Proof.MlDsa.X86.Sign.Hv p s₀ κ i); omega

/-- `ONES ← ONES + eax`, with `eax` the number of 1s of the hint's polynomial `nh - 1`. -/
theorem CS.addOnes {t nh : Nat} {fY fW : State → Nat → VG.Spec.MlDsa.Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s) (c' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s')
    (fr : Frame (FR s₀ [sc oONES 4] 0) s.mem s'.mem) {x : State → Nat}
    (v : VG.Proof.MlDsa.X86.Sign.scw s₀ s' oONES = VG.Proof.MlDsa.X86.Sign.scw s₀ s oONES + s.gpr .eax) (he : (s.gpr .eax).toNat = x s₀)
    (hb : ones s₀ + x s₀ < 2 ^ 32) : VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb (fun s₀ => ones s₀ + x s₀) s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (by ofs),
    h.ct_keep hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (by ofs),
    VG.Proof.MlDsa.X86.Sign.keepP hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (j := 0) (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs) h.c,
    h.fy.keep hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) (by ofs),
    h.fw.keep hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.wB]; omega) (by ofs),
    h.fh.keep hp ps (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs), ?_, ?_, h.nh⟩
  · rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) fr) (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)]
    exact h.ok
  · rw [v, h.ones]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, he, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := ones s₀) (by omega),
      Nat.mod_eq_of_lt hb]

/-- The hint's polynomial `nh`, made. -/
theorem CS.addHint {t nh : Nat} {fY fW : State → Nat → VG.Spec.MlDsa.Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s) (c' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s')
    (hn : nh < p.k) (fr : Frame (FR s₀ [pS (5 + nh)] 80) s.mem s'.mem)
    (hh : HintIs s'.mem (Buf.addr s₀ (pS (5 + nh))) 1 [VG.Proof.MlDsa.X86.Sign.Hv p s₀ (p.ℓ * t) nh]) :
    VG.Proof.MlDsa.X86.Sign.CS p t fY fW (nh + 1) okb ones s₀ s' :=
  have k := h.keep hp ps c' (by decide) fr (by ofs)
  { k with fh := k.fh.snoc hh, nh := hn }

/-- The okays of the checks of `ct₀` so far. -/
abbrev okH (p : Params) (t i : Nat) (s₀ : State) : Bool :=
  VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) p.ℓ && VG.Proof.MlDsa.X86.Sign.okR p s₀ (p.ℓ * t) p.k && VG.Proof.MlDsa.X86.Sign.okT p s₀ (p.ℓ * t) i

/-- `ct₀[i]` and its norm, `w - cs₂ + ct₀` in place of `w[i]`, and `h[i]`. -/
theorem hR_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t i : Nat) (hi : i < p.k) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t i) i (VG.Proof.MlDsa.X86.Sign.okH p t i) (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) i))
      (VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t (i + 1)) (i + 1) (VG.Proof.MlDsa.X86.Sign.okH p t (i + 1)) (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) (i + 1)))
      (hR P p i) := by
  have hj : VG.Proof.MlDsa.X86.Sign.t0B p + i < VG.Proof.MlDsa.X86.Sign.nS p := by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.t0B]; omega
  have hwj : VG.Proof.MlDsa.X86.Sign.wB p + i < VG.Proof.MlDsa.X86.Sign.nS p := by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.wB]; omega
  have hk := ps.hk
  have hβ := ps.hβ
  let H0 : State → State → Prop := VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t i) i (VG.Proof.MlDsa.X86.Sign.okH p t i) (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) i)
  let H1 : State → State → Prop := VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t i) i
    (fun s₀ => VG.Proof.MlDsa.X86.Sign.okH p t i s₀ && decide (normRq [VG.Proof.MlDsa.X86.Sign.CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) i)
  let H2 : State → State → Prop := VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t (i + 1)) i
    (fun s₀ => VG.Proof.MlDsa.X86.Sign.okH p t i s₀ && decide (normRq [VG.Proof.MlDsa.X86.Sign.CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) i)
  refine Piece.seq (B := fun s₀ s => H0 s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t3P) (multiplyNTT (chF (VG.Proof.MlDsa.X86.Sign.Cv p s₀ (p.ℓ * t))) (VG.Proof.MlDsa.X86.Sign.T0 p s₀ i)))
    (VG.Proof.MlDsa.X86.Sign.mul_piece F.mul (F.ok _ (by simp)) SC (VG.Impl.MlDsa.X86.Sign.oP 3) SC (VG.Impl.MlDsa.X86.Sign.oP 0) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.t0B p + i)) (by ofs)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (VG.Proof.MlDsa.X86.Sign.fam_at h.it.kd.dk.f0 hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofs), by
        rw [h.c.2, (VG.Proof.MlDsa.X86.Sign.fam_at h.it.kd.dk.f0 hi).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => H0 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (VG.Proof.MlDsa.X86.Sign.CT0v p s₀ (p.ℓ * t) i))
    (VG.Proof.MlDsa.X86.Sign.inPlace_piece (t := VG.Spec.MlDsa.nttInv) F.invNtt (F.ok _ (by simp)) t3P rfl (by ofs) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofs), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => H1 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (VG.Proof.MlDsa.X86.Sign.CT0v p s₀ (p.ℓ * t) i))
    (VG.Proof.MlDsa.X86.Sign.normAnd_piece F ps 3 (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) p.γ₂ (by omega) (fun s₀ => VG.Proof.MlDsa.X86.Sign.CT0v p s₀ (p.ℓ * t) i)) ?_
  refine Piece.seq (B := fun s₀ s => (H1 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (VG.Proof.MlDsa.X86.Sign.CT0v p s₀ (p.ℓ * t) i)) ∧
      PolyIs s.mem (Buf.addr s₀ t4P) (VG.Proof.MlDsa.X86.Sign.W'v p s₀ (p.ℓ * t) i))
    (VG.Proof.MlDsa.X86.Sign.copy_piece SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + i)) SC (VG.Impl.MlDsa.X86.Sign.oP 4) 256 (by decide) (by decide) (by ofs) (fun _ _ _ h => h.1.it.kd.ctx)
      fun s₀ s s' hp h c' fr hb => by
        have fr' : Frame (FR s₀ [t4P] 80) s.mem s'.mem := fr.mono (by simp)
        have hw := VG.Proof.MlDsa.X86.Sign.fam_at h.1.fw hi
        rw [VG.Proof.MlDsa.X86.Sign.hW_ge (Nat.lt_irrefl i)] at hw
        exact ⟨⟨h.1.keep hp ps c' (by decide) fr' (by ofs), VG.Proof.MlDsa.X86.Sign.keepP hp ps (by decide) fr' (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega)
          (by ofs) h.2⟩, polyIs_of_bytes hb hw⟩) ?_
  refine Piece.seq (B := fun s₀ s => H2 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ t4P) (VG.Proof.MlDsa.X86.Sign.W'v p s₀ (p.ℓ * t) i))
    (VG.Proof.MlDsa.X86.Sign.acc_piece (op := VG.Spec.MlDsa.add) F.add (F.ok _ (by simp)) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + i)) SC (VG.Impl.MlDsa.X86.Sign.oP 3) (by ofs)
      (fun _ _ _ h => ⟨h.1.1.it.kd.ctx, (VG.Proof.MlDsa.X86.Sign.fam_at h.1.1.fw hi).1, h.1.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.1.updW hp ps c' hi fr (by
        rw [(VG.Proof.MlDsa.X86.Sign.fam_at h.1.1.fw hi).2, h.1.2.2, VG.Proof.MlDsa.X86.Sign.hW_ge (Nat.lt_irrefl i)] at hq
        rw [VG.Proof.MlDsa.X86.Sign.hW_lt (Nat.lt_succ_self i)]; exact hq) fun j _ hji => VG.Proof.MlDsa.X86.Sign.upd_step hji,
        VG.Proof.MlDsa.X86.Sign.keepP hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs) h.2⟩) ?_
  refine Piece.seq (B := fun s₀ s => H2 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ t4P) (neg (VG.Proof.MlDsa.X86.Sign.CT0v p s₀ (p.ℓ * t) i)))
    (VG.Proof.MlDsa.X86.Sign.acc_piece (op := VG.Spec.MlDsa.sub) F.sub (F.ok _ (by simp)) SC (VG.Impl.MlDsa.X86.Sign.oP 4) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + i)) (by ofs)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1, (VG.Proof.MlDsa.X86.Sign.fam_at h.1.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofs), by
        rw [h.2.2, (VG.Proof.MlDsa.X86.Sign.fam_at h.1.fw hi).2, VG.Proof.MlDsa.X86.Sign.hW_lt (Nat.lt_succ_self i)] at hq
        rw [← VG.Proof.MlDsa.X86.Sign.sub_add_neg]; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t (i + 1)) (i + 1)
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okH p t i s₀ && decide (normRq [VG.Proof.MlDsa.X86.Sign.CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) i) s₀ s ∧
      (s.gpr .eax).toNat = hintOnes [VG.Proof.MlDsa.X86.Sign.Hv p s₀ (p.ℓ * t) i])
    (VG.Proof.MlDsa.X86.Sign.hint_piece F.makeHint (F.ok _ (by simp)) p.γ₂ ps.hγ₂ SC (VG.Impl.MlDsa.X86.Sign.oP 4) SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.wB p + i)) SC (VG.Impl.MlDsa.X86.Sign.oP (5 + i)) (by ofs)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1, (VG.Proof.MlDsa.X86.Sign.fam_at h.1.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hh he => by
        rw [h.2.2, (VG.Proof.MlDsa.X86.Sign.fam_at h.1.fw hi).2, VG.Proof.MlDsa.X86.Sign.hW_lt (Nat.lt_succ_self i)] at hh he
        exact ⟨h.1.addHint hp ps c' hi fr hh, he⟩) ?_
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.1.it.kd.ctx) (fun s₀ s hp h => VG.Proof.MlDsa.X86.Sign.wp_addOnes hp h.1.it.kd.ctx ps
    fun s' c' fr v => ?_) rfl
  have hb : VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) i + hintOnes [VG.Proof.MlDsa.X86.Sign.Hv p s₀ (p.ℓ * t) i] < 2 ^ 32 := by
    have := VG.Proof.MlDsa.X86.Sign.onesS_le (p := p) (s₀ := s₀) (κ := p.ℓ * t) i; have := VG.Proof.MlDsa.X86.Sign.hintOnes_le (VG.Proof.MlDsa.X86.Sign.Hv p s₀ (p.ℓ * t) i); omega
  have k := (h.1.addOnes hp ps c' fr (x := fun s₀ => hintOnes [VG.Proof.MlDsa.X86.Sign.Hv p s₀ (p.ℓ * t) i]) v h.2 hb).congr
    (fun _ _ => rfl) (fun _ _ => rfl) (okb' := VG.Proof.MlDsa.X86.Sign.okH p t (i + 1)) (by simp only [VG.Proof.MlDsa.X86.Sign.okH, VG.Proof.MlDsa.X86.Sign.okT, VG.Proof.MlDsa.X86.Sign.all_range_succ, Bool.and_assoc])
  exact { k with ones := by rw [k.ones, VG.Proof.MlDsa.X86.Sign.onesS_succ] }

/-! ## The 1s of the hint -/

theorem sign_bit {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b) >>> 31 = if a < b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  split
  · show _ = 1
    rw [Nat.shiftRight_eq_div_pow]; omega
  · show _ = 0
    rw [Nat.shiftRight_eq_div_pow]; omega

/-- The okays of all of the checks. -/
abbrev okAll (p : Params) (t : Nat) (s₀ : State) : Bool :=
  VG.Proof.MlDsa.X86.Sign.okH p t p.k s₀ && decide (VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) p.k ≤ p.ω)

/-- `OK ← OK ∧ ONES ≤ ω`. -/
theorem onesOk_piece (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t : Nat) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t p.k) p.k (VG.Proof.MlDsa.X86.Sign.okH p t p.k) (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) p.k))
      (VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t p.k) p.k (VG.Proof.MlDsa.X86.Sign.okAll p t) (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) p.k)) (.block (onesOk p)) := by
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.it.kd.ctx) (fun s₀ s hp h => ?_) rfl
  have hω := ps.hω
  have hk := ps.hk
  have hS := VG.Proof.MlDsa.X86.Sign.onesS_le (p := p) (s₀ := s₀) (κ := p.ℓ * t) p.k
  unfold onesOk
  refine VG.Proof.MlDsa.X86.Sign.wp_ldsc hp h.it.kd.ctx (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => VG.Proof.MlDsa.X86.Sign.wp_subi fun s₂ o₂ v₂ _ =>
    wp_shr (by decide) (by decide) fun s₃ o₃ v₃ => ?_
  have o := (o₁.trans o₂).trans o₃
  have c₃ := h.it.kd.ctx.only o (by simp) (by simp)
  have h₃ : VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t p.k) p.k (VG.Proof.MlDsa.X86.Sign.okH p t p.k) (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) p.k) s₀ s₃ :=
    h.keep hp ps c₃ (N := 0) (bs := []) (by decide) (by rw [o.mem]; exact Frame.refl _ _) (by simp)
  refine VG.Proof.MlDsa.X86.Sign.wp_andOK hp c₃ ps fun s' c' fr v => h₃.setOK hp ps c' fr (fun s₀ => decide (VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) p.k ≤ p.ω)) v ?_
  rw [v₃, v₂, v₁, h.ones, VG.Proof.MlDsa.X86.Sign.sign_bit (by omega) (by omega)]
  by_cases e : VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) p.k ≤ p.ω
  · rw [VG.Proof.MlDsa.Sign.ifp (by omega), decide_eq_true e]; rfl
  · rw [VG.Proof.MlDsa.Sign.ifn (by omega), decide_eq_false e]; rfl

/-! ## The end of the checks -/

/-- A piece keeps facts about the initial state. -/
theorem sp_pure {A B : State → State → Prop} {c : Prog isa} (φ : State → Prop) (h : VG.Proof.MlDsa.X86.Sign.SP p A B c) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => A s₀ s ∧ φ s₀) (fun s₀ s => B s₀ s ∧ φ s₀) c where
  wp s₀ s hp ha := (h.wp s₀ s hp ha.1).mono fun _ hb => ⟨hb, ha.2⟩
  ct s₀ s₀' hp hp' hq := (h.ct s₀ s₀' hp hp' hq).mono (fun _ _ ⟨a, a'⟩ => ⟨a.1, a'.1⟩) fun _ _ h => h

/-- Iteration `t` continues the loop. -/
abbrev contS (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (t : Nat) (s₀ : State) : Bool :=
  contV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) F.ballF t

/-- The checks of iteration `t` pass. -/
abbrev passS (p : Params) (t : Nat) (s₀ : State) : Prop := passV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) (p.ℓ * t)

/-- Iteration `t`, before `CNT ← CNT - 1`. -/
structure ED (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  kd : VG.Proof.MlDsa.X86.Sign.KD p s₀ s
  run : VG.Proof.MlDsa.X86.Sign.Run p F t s₀
  cnt : VG.Proof.MlDsa.X86.Sign.scw s₀ s oCNT = if VG.Proof.MlDsa.X86.Sign.contS p F t s₀ then BitVec.ofNat 32 (814 - t) else 1
  kap : VG.Proof.MlDsa.X86.Sign.contS p F t s₀ = true → VG.Proof.MlDsa.X86.Sign.scw s₀ s oKAP = BitVec.ofNat 32 (p.ℓ * (t + 1))
  ok : VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = if (F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) && decide (VG.Proof.MlDsa.X86.Sign.passS p t s₀)) then 1 else 0
  out : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = true → VG.Proof.MlDsa.X86.Sign.passS p t s₀ →
    VG.Proof.MlDsa.X86.Sign.Fam s₀ s.mem (VG.Proof.MlDsa.X86.Sign.yB p) p.ℓ (VG.Proof.MlDsa.X86.Sign.Zv p s₀ (p.ℓ * t)) ∧ VG.Proof.MlDsa.X86.Sign.HF s₀ s.mem p.k (VG.Proof.MlDsa.X86.Sign.Hv p s₀ (p.ℓ * t)) ∧
      bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)
  none : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = false → VG.Spec.MlDsa.sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = none

theorem KD.keep {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.KD p s₀ s) (c' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s')
    {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, VG.Proof.MlDsa.X86.Sign.OutK p p.ℓ p.k p.k c ∧ VG.Proof.MlDsa.X86.Sign.Out p oMS (oMS + 64) c) : VG.Proof.MlDsa.X86.Sign.KD p s₀ s' :=
  ⟨c', h.dk.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hN fr fun c hc => (hb c hc).1,
    by rw [VG.Proof.MlDsa.X86.Sign.keepB hp hN fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2, h.ms]⟩

theorem okAll_eq {t : Nat} {s₀ : State} : VG.Proof.MlDsa.X86.Sign.okAll p t s₀ = decide (VG.Proof.MlDsa.X86.Sign.passS p t s₀) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact pass_iff.symm

/-- Whether the checks passed, in a run that reaches iteration `t` and whose `SampleInBall` succeeded. -/
def passB (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (t : Nat) (s₀ : State) : Bool :=
  decide (VG.Proof.MlDsa.X86.Sign.Run p F t s₀ ∧ F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = true ∧ VG.Proof.MlDsa.X86.Sign.passS p t s₀)

theorem passB_eq {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : VG.Proof.MlDsa.X86.Sign.PS p) (hq : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') :
    VG.Proof.MlDsa.X86.Sign.passB p F t s₀ = VG.Proof.MlDsa.X86.Sign.passB p F t s₀' := by
  unfold VG.Proof.MlDsa.X86.Sign.passB
  by_cases h : VG.Proof.MlDsa.X86.Sign.Run p F t s₀
  · have h' := (VG.Proof.MlDsa.X86.Sign.run_iff ps hq).mp h
    obtain ⟨ect, hb⟩ := VG.Proof.MlDsa.X86.Sign.run_at ps hq h
    by_cases hs : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = true
    · have hs' : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀' (p.ℓ * t)) = true := by rw [← ect]; exact hs
      exact decide_eq_decide.mpr ⟨fun ⟨_, _, a⟩ => ⟨h', hs', (hb hs).1.mp a⟩, fun ⟨_, _, a⟩ => ⟨h, hs, (hb hs).1.mpr a⟩⟩
    · have hs' : ¬ F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀' (p.ℓ * t)) = true := by rw [← ect]; exact hs
      exact decide_eq_decide.mpr ⟨fun ⟨_, a, _⟩ => absurd a hs, fun ⟨_, a, _⟩ => absurd a hs'⟩
  · exact decide_eq_decide.mpr ⟨fun ⟨a, _⟩ => absurd a h, fun ⟨a, _⟩ => absurd ((VG.Proof.MlDsa.X86.Sign.run_iff ps hq).mpr a) h⟩

theorem CS.ofMem {t nh : Nat} {fY fW : State → Nat → VG.Spec.MlDsa.Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (h : VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s') (c : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s)
    (hm : s.mem = s'.mem) : VG.Proof.MlDsa.X86.Sign.CS p t fY fW nh okb ones s₀ s :=
  h.keep hp ps c (N := 0) (bs := []) (by decide) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- The state after the checks. -/
abbrev CE (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (t : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t p.k) p.k (VG.Proof.MlDsa.X86.Sign.okAll p t) (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) p.k) s₀ s ∧
    (VG.Proof.MlDsa.X86.Sign.Run p F t s₀ ∧ F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = true)

/-- `CNT ← 1` if the checks passed, and `κ ← κ + ℓ` otherwise. -/
theorem checksEnd_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t : Nat) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.CE p F t) (VG.Proof.MlDsa.X86.Sign.ED p F t) (ifOkElse (.block (st32 oCNT 1)) (.block (nextKappa p))) := by
  refine VG.Proof.MlDsa.X86.Sign.okIte_piece (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (VG.Proof.MlDsa.X86.Sign.passB p F t) (fun s₀ s hp h => ⟨h.1.it.kd.ctx, ?_⟩)
    (fun s₀ s₀' _ _ hq => VG.Proof.MlDsa.X86.Sign.passB_eq ps hq) ?_ ?_
  · rw [h.1.ok, VG.Proof.MlDsa.X86.Sign.okAll_eq]
    simp only [VG.Proof.MlDsa.X86.Sign.passB, h.2.1, h.2.2, true_and]
  · refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.1.choose_spec.2.1) (fun s₀ s₁ hp h => ?_) rfl
    obtain ⟨⟨s, ha, c₁, m₁⟩, hb⟩ := h
    have h₁ := ha.1.ofMem hp ps c₁ m₁
    simp only [VG.Proof.MlDsa.X86.Sign.passB, decide_eq_true_iff] at hb
    rw [← List.append_nil (st32 oCNT 1)]
    refine VG.Proof.MlDsa.X86.Sign.wp_st32 hp c₁ (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) 1 fun s' c' fr v => WP.block_nil_iff.mpr ?_
    have fr' := VG.Proof.MlDsa.X86.Sign.fr0 hp (N := 80) (by decide) fr
    have hc : VG.Proof.MlDsa.X86.Sign.contS p F t s₀ = false := by
      simp only [VG.Proof.MlDsa.X86.Sign.contS, contV, hb.2.2, decide_true, Bool.not_true, Bool.and_false]
    have hk := h₁.nh
    refine ⟨h₁.it.kd.keep hp ps c' (by decide) fr' (by ofs), hb.1, by rw [hc, v]; rfl, (fun e => by rw [hc] at e; cases e),
      ?_, fun _ _ => ⟨?_, h₁.fh.keep hp ps (by decide) fr' (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs),
        h₁.ct_keep hp ps (by decide) fr' (by ofs)⟩, (fun e => by rw [hb.2.1] at e; cases e)⟩
    · rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) fr' (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs), ← VG.Proof.MlDsa.X86.Sign.scw, h₁.ok, VG.Proof.MlDsa.X86.Sign.okAll_eq,
        hb.2.1, Bool.true_and]
    · exact (h₁.fy.keep hp ps (by decide) fr' (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) (by ofs)).congr fun j hj => VG.Proof.MlDsa.X86.Sign.zY_lt hj
  · refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.1.choose_spec.2.1) (fun s₀ s₁ hp h => ?_) rfl
    obtain ⟨⟨s, ha, c₁, m₁⟩, hb⟩ := h
    have h₁ := ha.1.ofMem hp ps c₁ m₁
    have hpass : ¬ VG.Proof.MlDsa.X86.Sign.passS p t s₀ := fun hq => by
      simp only [VG.Proof.MlDsa.X86.Sign.passB, decide_eq_false_iff_not] at hb; exact hb ⟨ha.2.1, ha.2.2, hq⟩
    have hc : VG.Proof.MlDsa.X86.Sign.contS p F t s₀ = true := by
      simp only [VG.Proof.MlDsa.X86.Sign.contS, contV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨ha.2.2, hpass⟩
    unfold nextKappa
    refine VG.Proof.MlDsa.X86.Sign.wp_ldsc hp c₁ (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun s₂ o₂ v₂ => wp_addi fun s₃ o₃ v₃ => ?_
    have o := o₂.trans o₃
    have c₃ := c₁.only o (by simp) (by simp)
    refine VG.Proof.MlDsa.X86.Sign.wp_stsc hp c₃ (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) fun s' c' g' m' => WP.block_nil_iff.mpr ?_
    have fr : Frame (FR s₀ [sc oKAP 4] 80) s₁.mem s'.mem := VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) (by
      rw [m', o.mem]; exact frW32 (Y := VG.Proof.MlDsa.X86.Sign.Y p))
    refine ⟨h₁.it.kd.keep hp ps c' (by decide) fr (by ofs), ha.2.1, ?_, fun _ => ?_, ?_,
      (fun _ e => absurd e hpass), (fun e => by rw [ha.2.2] at e; cases e)⟩
    · rw [hc, VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs), ← VG.Proof.MlDsa.X86.Sign.scw, h₁.it.cnt]; rfl
    · rw [VG.Proof.MlDsa.X86.Sign.scw, m', Mem.readW_writeW_self32, v₃, v₂, h₁.it.kap, ← BitVec.ofNat_add, Nat.mul_succ]
    · rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs), ← VG.Proof.MlDsa.X86.Sign.scw, h₁.ok, VG.Proof.MlDsa.X86.Sign.okAll_eq,
        decide_eq_false hpass, Bool.and_false]

/-! ## The checks -/

/-- The checks of iteration `t`, once `SampleInBall` succeeded. -/
theorem checks_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t : Nat) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlDsa.X86.Sign.KP p F t s₀ s ∧ PolyIs s.mem (Buf.addr s₀ cP) (toRq (VG.Proof.MlDsa.X86.Sign.Cv p s₀ (p.ℓ * t)))) (VG.Proof.MlDsa.X86.Sign.ED p F t)
      (checks P p) := by
  have hk := ps.hk
  have hl := ps.hl
  let φ : State → Prop := fun s₀ => VG.Proof.MlDsa.X86.Sign.Run p F t s₀ ∧ F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = true
  unfold checks
  refine Piece.seq (B := fun s₀ s => (VG.Proof.MlDsa.X86.Sign.CC p t s₀ s ∧ PolyIs s.mem (Buf.addr s₀ cP) (chF (VG.Proof.MlDsa.X86.Sign.Cv p s₀ (p.ℓ * t)))) ∧ φ s₀)
    ((VG.Proof.MlDsa.X86.Sign.inPlace_piece (t := VG.Spec.MlDsa.ntt) F.ntt (F.ok _ (by simp)) cP rfl (by ofs) (fun _ _ _ h => ⟨h.1.cc.cw.cm.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.cc.keep hp ps c' (by decide) fr (by ofs), by rw [h.2.2] at hq; exact hq⟩).mono
        (fun _ _ _ h => h) (fun _ _ _ h => h) |> VG.Proof.MlDsa.X86.Sign.sp_pure φ |>.mono (fun _ _ _ h => ⟨h, h.1.run, h.1.ball⟩)
        fun _ _ _ h => h) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t 0) (fun s₀ => VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) 0) (fun _ => 0) s₀ s ∧ φ s₀) (VG.Proof.MlDsa.X86.Sign.sp_pure φ (VG.Proof.MlDsa.X86.Sign.checksInit_piece ps t)) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (fun s₀ => VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) p.ℓ) (fun _ => 0) s₀ s ∧ φ s₀) (VG.Proof.MlDsa.X86.Sign.sp_pure φ ?_) ?_
  · have := VG.Proof.MlDsa.X86.Sign.seqR_piece (p := p) (I := fun r => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t r) (fun s₀ => VG.Proof.MlDsa.X86.Sign.Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) r) (fun _ => 0)) 0 p.ℓ fun r _ hr => VG.Proof.MlDsa.X86.Sign.zR_piece F ps t r (by omega)
    simpa using this
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.rW p t p.k) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) p.ℓ && VG.Proof.MlDsa.X86.Sign.okR p s₀ (p.ℓ * t) p.k) (fun _ => 0) s₀ s ∧ φ s₀) (VG.Proof.MlDsa.X86.Sign.sp_pure φ ?_) ?_
  · have := VG.Proof.MlDsa.X86.Sign.seqR_piece (p := p) (I := fun i => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.rW p t i) 0
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.okZ p s₀ (p.ℓ * t) p.ℓ && VG.Proof.MlDsa.X86.Sign.okR p s₀ (p.ℓ * t) i) (fun _ => 0)) 0 p.k fun i _ hi =>
        VG.Proof.MlDsa.X86.Sign.r0R_piece F ps t i (by omega)
    simp only [Nat.zero_add] at this
    exact this.mono (fun s₀ s _ h => h.congr (fun _ _ => rfl) (fun j _ => (VG.Proof.MlDsa.X86.Sign.rW_ge (Nat.not_lt_zero j)).symm)
      (by simp [VG.Proof.MlDsa.X86.Sign.okR])) fun _ _ _ h => h
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t p.k) p.k (VG.Proof.MlDsa.X86.Sign.okH p t p.k)
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) p.k) s₀ s ∧ φ s₀) (VG.Proof.MlDsa.X86.Sign.sp_pure φ ?_) ?_
  · have := VG.Proof.MlDsa.X86.Sign.seqR_piece (p := p) (I := fun i => VG.Proof.MlDsa.X86.Sign.CS p t (VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (VG.Proof.MlDsa.X86.Sign.hW p t i) i (VG.Proof.MlDsa.X86.Sign.okH p t i)
      (fun s₀ => VG.Proof.MlDsa.X86.Sign.onesS p s₀ (p.ℓ * t) i)) 0 p.k fun i _ hi => VG.Proof.MlDsa.X86.Sign.hR_piece F ps t i (by omega)
    simp only [Nat.zero_add] at this
    refine this.mono (fun s₀ s _ h => ?_) fun _ _ _ h => h
    have h' := h.congr (fY' := VG.Proof.MlDsa.X86.Sign.zY p t p.ℓ) (fW' := VG.Proof.MlDsa.X86.Sign.hW p t 0) (okb' := VG.Proof.MlDsa.X86.Sign.okH p t 0) (fun _ _ => rfl)
      (fun j hj => by rw [VG.Proof.MlDsa.X86.Sign.rW_lt hj, VG.Proof.MlDsa.X86.Sign.hW_ge (Nat.not_lt_zero j)]) (by simp [VG.Proof.MlDsa.X86.Sign.okH, VG.Proof.MlDsa.X86.Sign.okT])
    exact { h' with fh := fun j hj => absurd hj (Nat.not_lt_zero _), ones := by rw [h'.ones]; rfl, nh := Nat.zero_le _ }
  refine Piece.seq (B := VG.Proof.MlDsa.X86.Sign.CE p F t) (VG.Proof.MlDsa.X86.Sign.sp_pure φ (VG.Proof.MlDsa.X86.Sign.onesOk_piece ps t)) (VG.Proof.MlDsa.X86.Sign.checksEnd_piece F ps t)

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseL`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the rejection sampling loop

Iteration `t` runs the commitment, `SampleInBall`, and the checks if it
succeeded, and ends with `CNT ← CNT - 1` (`iter_piece`). The loop runs `NI`
iterations (`loop_piece`): after `t < NI` of them, iteration `t` is next
(`IT`); after all of them, the last one's outcome is in `OK`, with `c̃`, `z`
and the hint if it succeeded (`Fin`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-- The outcome of the last iteration, `u`. -/
structure Fin' (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (u : Nat) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s
  run : VG.Proof.MlDsa.X86.Sign.Run p F u s₀
  ok : VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = if (F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * u)) && decide (VG.Proof.MlDsa.X86.Sign.passS p u s₀)) then 1 else 0
  out : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * u)) = true → VG.Proof.MlDsa.X86.Sign.passS p u s₀ →
    VG.Proof.MlDsa.X86.Sign.Fam s₀ s.mem (VG.Proof.MlDsa.X86.Sign.yB p) p.ℓ (VG.Proof.MlDsa.X86.Sign.Zv p s₀ (p.ℓ * u)) ∧ VG.Proof.MlDsa.X86.Sign.HF s₀ s.mem p.k (VG.Proof.MlDsa.X86.Sign.Hv p s₀ (p.ℓ * u)) ∧
      bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * u)
  none : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * u)) = false → VG.Spec.MlDsa.sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * u)) = none

/-- After `t` iterations. -/
structure LI (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  good : VG.Proof.MlDsa.X86.Sign.Good p F s₀
  le : t ≤ VG.Proof.MlDsa.X86.Sign.NI p F s₀
  it : t < VG.Proof.MlDsa.X86.Sign.NI p F s₀ → VG.Proof.MlDsa.X86.Sign.IT p t s₀ s
  fin : t = VG.Proof.MlDsa.X86.Sign.NI p F s₀ → VG.Proof.MlDsa.X86.Sign.Fin' p F (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1) s₀ s

/-- A store to the word at `o`, which keeps the flags. -/
theorem wp_stscZ {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s) {o : Nat} (hc : (VG.Proof.MlDsa.X86.Sign.Y p).okW (sc o 4) = true)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s' → (∀ x, s'.gpr x = s.gpr x) → s'.zf = s.zf →
      s'.mem = s.mem.writeW (Buf.addr s₀ (sc o 4)) (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ .esi o) r :: is)) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  have hin : InRegions s.wr (Buf.addr s₀ (sc o 4)) 4 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  refine VG.Proof.MlKem.X86.wp_store (by rw [VG.Proof.MlDsa.X86.Sign.ea_sc h o 4]; exact hin) ?_
  have c := VG.Proof.MlDsa.X86.Sign.ctx_write hp h hc (w := 32) (by decide) (s.gpr r)
  refine k _ ?_ (fun _ => rfl) rfl (by rw [VG.Proof.MlDsa.X86.Sign.ea_sc h o 4])
  rw [VG.Proof.MlDsa.X86.Sign.ea_sc h o 4]; exact c

theorem ofNat_sub_one {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 32) : BitVec.ofNat 32 x - 1 = BitVec.ofNat 32 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : (1 : BitVec 32).toNat = 1 := rfl
  rw [this]
  omega

/-- `CNT ← CNT - 1`, which sets `ZF` when the loop ends. -/
theorem tail_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t : Nat) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.ED p F t) (fun s₀ s => VG.Proof.MlDsa.X86.Sign.LI p F (t + 1) s₀ s ∧ isa.eval .ne s = some (decide (t + 1 < VG.Proof.MlDsa.X86.Sign.NI p F s₀)))
      (.block [.mov .eax (.mem (at_ .esi oCNT)), .alu .sub .eax (.imm 1), .store (at_ .esi oCNT) .eax]) := by
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.kd.ctx) (fun s₀ s hp h => ?_) rfl
  refine VG.Proof.MlDsa.X86.Sign.wp_ldsc hp h.kd.ctx (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => VG.Proof.MlDsa.X86.Sign.wp_subi fun s₂ o₂ v₂ z₂ => ?_
  have o := o₁.trans o₂
  have c₂ := h.kd.ctx.only o (by simp) (by simp)
  refine VG.Proof.MlDsa.X86.Sign.wp_stscZ hp c₂ (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) fun s' c' g' z' m' => WP.block_nil_iff.mpr ?_
  have fr : Frame (FR s₀ [sc oCNT 4] 80) s.mem s'.mem := VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) (by
    rw [m', o.mem]; exact frW32 (Y := VG.Proof.MlDsa.X86.Sign.Y p))
  have hrun := h.run
  have hNI := VG.Proof.MlDsa.X86.Sign.NI_good hrun.1
  have ht := hrun.2
  have hlt := hrun.lt
  have hnext : t + 1 < VG.Proof.MlDsa.X86.Sign.NI p F s₀ ↔ VG.Proof.MlDsa.X86.Sign.contS p F t s₀ = true ∧ t + 1 < 814 := by
    rw [hNI]; exact nIt_next _ (by have := ht; rw [hNI] at this; exact this)
  have hcnt : VG.Proof.MlDsa.X86.Sign.scw s₀ s' oCNT = VG.Proof.MlDsa.X86.Sign.scw s₀ s oCNT - 1 := by
    rw [VG.Proof.MlDsa.X86.Sign.scw, m', Mem.readW_writeW_self32, v₂, v₁]
  have hz : isa.eval .ne s' = some (decide (t + 1 < VG.Proof.MlDsa.X86.Sign.NI p F s₀)) := by
    show s'.zf.map (!·) = _
    rw [z', z₂, v₁, h.cnt]
    cases e : VG.Proof.MlDsa.X86.Sign.contS p F t s₀
    · simp only [e, Bool.false_eq_true, false_and, iff_false] at hnext
      rw [decide_eq_false hnext]; simp
    · simp only [e, true_and] at hnext
      simp only [↓reduceIte]
      rw [show decide (t + 1 < VG.Proof.MlDsa.X86.Sign.NI p F s₀) = decide (t + 1 < 814) from decide_eq_decide.mpr hnext]
      by_cases e' : t + 1 < 814
      · rw [decide_eq_true e']
        rw [VG.Proof.MlDsa.X86.Sign.ofNat_sub_one (by omega) (by omega)]
        have : (BitVec.ofNat 32 (814 - t - 1) == 0) = false := by
          apply beq_eq_false_iff_ne.mpr
          intro h0
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          exact absurd this (by show ¬ (814 - t - 1 = 0); omega)
        rw [this]; rfl
      · rw [decide_eq_false e', show 814 - t = 1 by omega]; rfl
  refine ⟨⟨hrun.1, ht, fun ht' => ?_, fun ht' => ?_⟩, hz⟩
  · have hc : VG.Proof.MlDsa.X86.Sign.contS p F t s₀ = true := (hnext.mp ht').1
    refine ⟨h.kd.keep hp ps c' (by decide) fr (by ofs), ?_, ?_, (hnext.mp ht').2⟩
    · rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.kap hc
    · rw [hcnt, h.cnt, hc]
      simp only [↓reduceIte]
      rw [VG.Proof.MlDsa.X86.Sign.ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  · rw [← ht', Nat.add_sub_cancel]
    refine ⟨c', hrun, ?_, fun hb hq => ?_, h.none⟩
    · rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (by decide) fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ok
    · obtain ⟨f1, f2, f3⟩ := h.out hb hq
      have := ps.hcLen
      exact ⟨f1.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) (by ofs),
        f2.keep hp ps (by decide) fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) (by ofs),
        by rw [VG.Proof.MlDsa.X86.Sign.keepB hp (by decide) fr (by ofs) (by ofs), f3]⟩

/-- `OK ← 0` and `CNT ← 1`, when `SampleInBall` failed. -/
theorem ballFail_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t : Nat) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => (∃ s', VG.Proof.MlDsa.X86.Sign.IB p F t s₀ s' ∧ VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ s.mem = s'.mem ∧ s.zf = some (!VG.Proof.MlDsa.X86.Sign.ballB p F t s₀)) ∧
      VG.Proof.MlDsa.X86.Sign.ballB p F t s₀ = false) (VG.Proof.MlDsa.X86.Sign.ED p F t) (.block (st32 oOK 0 ++ st32 oCNT 1)) := by
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.1.choose_spec.2.1) (fun s₀ s hp h => ?_) rfl
  obtain ⟨⟨s', ib, c, m, _⟩, hb⟩ := h
  have hf : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = false := by rw [← VG.Proof.MlDsa.X86.Sign.ballB_of ib.run]; exact hb
  have kd := ib.cc.cw.cm.it.kd.keep hp ps c (N := 0) (bs := []) (by decide) (by rw [m]; exact Frame.refl _ _)
    (by simp)
  refine VG.Proof.MlDsa.X86.Sign.wp_st32 hp c (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) 0 fun s₁ c₁ f₁ v₁ => ?_
  rw [← List.append_nil (st32 oCNT 1)]
  refine VG.Proof.MlDsa.X86.Sign.wp_st32 hp c₁ (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) 1 fun s₂ c₂ f₂ v₂ => WP.block_nil_iff.mpr ?_
  have kd₁ := kd.keep hp ps c₁ (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) f₁) (by ofs)
  have hc : VG.Proof.MlDsa.X86.Sign.contS p F t s₀ = false := by simp only [VG.Proof.MlDsa.X86.Sign.contS, contV, hf, Bool.false_and]
  refine ⟨kd₁.keep hp ps c₂ (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) f₂) (by ofs), ib.run, by rw [hc, v₂]; rfl,
    (fun e => by rw [hc] at e; cases e), ?_, (fun e => by rw [hf] at e; cases e), fun _ => ib.no hf⟩
  rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) f₂) (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs), ← VG.Proof.MlDsa.X86.Sign.scw,
    v₁, hf, Bool.false_and]; rfl

/-- Iteration `t`. -/
theorem iter_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (t : Nat) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlDsa.X86.Sign.LI p F t s₀ s ∧ t < VG.Proof.MlDsa.X86.Sign.NI p F s₀)
      (fun s₀ s => VG.Proof.MlDsa.X86.Sign.LI p F (t + 1) s₀ s ∧ isa.eval .ne s = some (decide (t + 1 < VG.Proof.MlDsa.X86.Sign.NI p F s₀))) (iter P p) := by
  unfold iter
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.CC p t s₀ s ∧ VG.Proof.MlDsa.X86.Sign.Run p F t s₀)
    ((VG.Proof.MlDsa.X86.Sign.sp_pure (VG.Proof.MlDsa.X86.Sign.Run p F t) (VG.Proof.MlDsa.X86.Sign.commit_piece F ps t)).mono (fun s₀ s _ h =>
      ⟨⟨h.1.it h.2, fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
        h.1.good, h.2⟩) fun _ _ _ h => h) ?_
  refine Piece.seq (VG.Proof.MlDsa.X86.Sign.ballCall_piece F ps t) ?_
  refine Piece.seq (VG.Proof.MlDsa.X86.Sign.ballTest_piece F t) ?_
  refine Piece.seq (Piece.ite (VG.Proof.MlDsa.X86.Sign.ballB p F t) (fun s₀ s _ h => ?_) (fun s₀ s₀' _ _ hq => VG.Proof.MlDsa.X86.Sign.ballB_eq ps hq)
    ((VG.Proof.MlDsa.X86.Sign.checks_piece F ps t).mono (fun s₀ s hp h => ?_) fun _ _ _ h => h) (VG.Proof.MlDsa.X86.Sign.ballFail_piece F ps t)) (VG.Proof.MlDsa.X86.Sign.tail_piece F ps t)
  · show s.zf.map (!·) = _
    rw [h.choose_spec.2.2.2]; cases VG.Proof.MlDsa.X86.Sign.ballB p F t s₀ <;> rfl
  · obtain ⟨⟨s', ib, c, m, _⟩, hb⟩ := h
    have hs : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * t)) = true := by rw [← VG.Proof.MlDsa.X86.Sign.ballB_of ib.run]; exact hb
    exact ⟨⟨ib.cc.ofMem hp ps c m, ib.run, hs⟩, by rw [m]; exact ib.yes hs⟩

/-- `κ ← 0`, `CNT ← 814`, and the loop. -/
theorem signLoop_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => VG.Proof.MlDsa.X86.Sign.KD p s₀ s ∧ VG.Proof.MlDsa.X86.Sign.Good p F s₀) (fun s₀ s => VG.Proof.MlDsa.X86.Sign.Fin' p F (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1) s₀ s) (Impl.MlDsa.X86.Sign.signLoop P p) := by
  unfold Impl.MlDsa.X86.Sign.signLoop
  refine Piece.seq (B := VG.Proof.MlDsa.X86.Sign.LI p F 0) ?_ ((VG.Proof.MlDsa.X86.Sign.loopN (VG.Proof.MlDsa.X86.Sign.NI p F) (VG.Proof.MlDsa.X86.Sign.LI p F) (fun s₀ _ => VG.Proof.MlDsa.X86.Sign.NI_pos (p := p) F s₀)
    (fun s₀ s₀' _ _ hq => VG.Proof.MlDsa.X86.Sign.NI_eq ps hq) fun t => VG.Proof.MlDsa.X86.Sign.iter_piece F ps t).mono (fun _ _ _ h => h)
      fun s₀ s _ h => h.fin rfl)
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.1.ctx) (fun s₀ s hp h => ?_) rfl
  refine VG.Proof.MlDsa.X86.Sign.wp_st32 hp h.1.ctx (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) 0 fun s₁ c₁ f₁ v₁ => ?_
  rw [← List.append_nil (st32 oCNT 814)]
  refine VG.Proof.MlDsa.X86.Sign.wp_st32 hp c₁ (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) 814 fun s₂ c₂ f₂ v₂ => WP.block_nil_iff.mpr ?_
  have kd₁ := h.1.keep hp ps c₁ (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) f₁) (by ofs)
  have hpos := VG.Proof.MlDsa.X86.Sign.NI_pos (p := p) F s₀
  refine ⟨h.2, Nat.zero_le _, fun _ => ⟨kd₁.keep hp ps c₂ (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) f₂) (by ofs),
    ?_, v₂, by decide⟩, fun e => absurd e (by omega)⟩
  rw [VG.Proof.MlDsa.X86.Sign.scw, VG.Proof.MlDsa.X86.Sign.keepW' hp (N := 80) (by decide) (VG.Proof.MlDsa.X86.Sign.fr0 hp (by decide) f₂) (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (by ofs), ← VG.Proof.MlDsa.X86.Sign.scw,
    v₁]; rfl

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseO`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the signature

Once an iteration passed, `sig` is `c̃` (`outCopy_piece`), the `BitPack` of
`z` (`packZ_piece`), in range by the check of its norm (`inRange_of_norm`),
and `HintBitPack(h)` (`hpack_piece`), whose 1s are at most `ω` by the check of
their number, and whose leakage, the hint, two runs whose checks pass agree on
(`hint_list`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : VG.Spec.MlDsa.Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem inRange_of_norm {m : Mem} {a : Addr} {f : VG.Spec.MlDsa.Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) :
    ∀ i < n, -((γ - 1 : Nat) : Int) ≤ modPm (coeffAt m a i).toNat q ∧ modPm (coeffAt m a i).toNat q ≤ γ := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [VG.Proof.MlDsa.X86.Sign.coeff_val h hi]
  simp only [normZq] at this
  omega

/-! ## The hint -/

theorem coeff_slot {m : Mem} {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {i j : Nat} (hi : i < p.k) :
    coeffAt m (Buf.addr s₀ (sc (VG.Impl.MlDsa.X86.Sign.oP 5) (1024 * p.k))) (256 * i + j) = coeffAt m (Buf.addr s₀ (pS (5 + i))) j := by
  have e : Buf.addr s₀ (pS (5 + i)) = Buf.addr s₀ (sc (VG.Impl.MlDsa.X86.Sign.oP 5) (1024 * p.k)) + BitVec.ofNat 64 (1024 * i) := by
    show Buf.addr s₀ (sc (VG.Impl.MlDsa.X86.Sign.oP (5 + i)) 1024) = _
    rw [show VG.Impl.MlDsa.X86.Sign.oP (5 + i) = VG.Impl.MlDsa.X86.Sign.oP 5 + 1024 * i by simp only [VG.Impl.MlDsa.X86.Sign.oP]; omega]
    exact VG.Proof.MlDsa.X86.Sign.addr_off hp (by ofs) (by ofs)
  simp only [coeffAt]
  rw [e, BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega]

theorem hintAt_of {m : Mem} {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {f : Nat → Vector Bool n}
    (h : VG.Proof.MlDsa.X86.Sign.HF s₀ m p.k f) : hintAt m (Buf.addr s₀ (sc (VG.Impl.MlDsa.X86.Sign.oP 5) (1024 * p.k))) p.k = (List.range p.k).map f := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have e := (h i hi).2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
  rw [Vector.getElem_ofFn, VG.Proof.MlDsa.X86.Sign.coeff_slot hp ps hi, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = ((List.range k).map fun j => hintOnes [f j]).sum := by
  simp only [hintOnes, List.map_map, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rfl

/-- The coefficients of the hint, as the list `hbitsV` of its bits. -/
theorem hint_list {m : Mem} {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {f : Nat → Vector Bool n}
    (h : VG.Proof.MlDsa.X86.Sign.HF s₀ m p.k f) :
    (List.range (256 * p.k)).map (fun i => (coeffAt m (Buf.addr s₀ (sc (VG.Impl.MlDsa.X86.Sign.oP 5) (1024 * p.k))) i).toNat) =
      ((List.range p.k).map f).flatMap fun hi => hi.toList.map Bool.toNat := by
  suffices ∀ k ≤ p.k, (List.range (256 * k)).map (fun i => (coeffAt m (Buf.addr s₀ (sc (VG.Impl.MlDsa.X86.Sign.oP 5) (1024 * p.k))) i).toNat) =
      ((List.range k).map f).flatMap fun hi => hi.toList.map Bool.toNat from this p.k (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 256 * (k + 1) = 256 * k + 256 by omega, List.range_add, List.map_append, ih (by omega),
      List.range_succ (n := k), List.map_append, List.flatMap_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
    refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
    simp only [List.length_map, List.length_range] at h₁
    have e := (h k (by omega)).2 0 (by decide) j h₁
    simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
    simp only [List.getElem_map, List.getElem_range, Function.comp, Vector.getElem_toList, VG.Proof.MlDsa.X86.Sign.coeff_slot hp ps (by omega : k < p.k),
      e, getElem!_pos (f k) j h₁]
    cases (f k)[j] <;> rfl

/-! ## The signature -/

/-- The `BitPack` of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (s₀ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => VG.Spec.MlDsa.bitPack ((VG.Proof.MlDsa.X86.Sign.Zv p s₀ κ j).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁

/-- Before the signature, the last iteration `U s₀` having passed; with the
first `r` polynomials of `z` packed after `c̃` in `sig`. -/
structure OS (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (U : State → Nat) (r : Nat) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s
  fy : VG.Proof.MlDsa.X86.Sign.Fam s₀ s.mem (VG.Proof.MlDsa.X86.Sign.yB p) p.ℓ (VG.Proof.MlDsa.X86.Sign.Zv p s₀ (p.ℓ * U s₀))
  fh : VG.Proof.MlDsa.X86.Sign.HF s₀ s.mem p.k (VG.Proof.MlDsa.X86.Sign.Hv p s₀ (p.ℓ * U s₀))
  run : VG.Proof.MlDsa.X86.Sign.Run p F (U s₀) s₀
  ball : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * U s₀)) = true
  pass : VG.Proof.MlDsa.X86.Sign.passS p (U s₀) s₀
  ok1 : VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = 1
  sig : bytesAt s.mem (Buf.addr s₀ (bSig 0 (cLen p + zLen p * r))) (cLen p + zLen p * r) =
    VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * U s₀) ++ VG.Proof.MlDsa.X86.Sign.zEnc p s₀ (p.ℓ * U s₀) r

/-- A write of `sig` keeps `z` and the hint. -/
theorem sigKeep {s₀ : State} (hp : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {m m' : Mem} {fz : Nat → VG.Spec.MlDsa.Poly} {fh : Nat → Vector Bool n}
    (hz : VG.Proof.MlDsa.X86.Sign.Fam s₀ m (VG.Proof.MlDsa.X86.Sign.yB p) p.ℓ fz) (hh : VG.Proof.MlDsa.X86.Sign.HF s₀ m p.k fh) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    (fr : Frame (FR s₀ bs N) m m') (hb : ∀ c ∈ bs, (VG.Proof.MlDsa.X86.Sign.Y p).ok c = true ∧ c.arg = 3) :
    VG.Proof.MlDsa.X86.Sign.Fam s₀ m' (VG.Proof.MlDsa.X86.Sign.yB p) p.ℓ fz ∧ VG.Proof.MlDsa.X86.Sign.HF s₀ m' p.k fh ∧
      m'.readW (Buf.addr s₀ (sc oOK 4)) 32 = m.readW (Buf.addr s₀ (sc oOK 4)) 32 :=
  ⟨hz.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS, VG.Proof.MlDsa.X86.Sign.yB]; omega) fun c hc => ⟨(hb c hc).1, fun e => by
      rw [(hb c hc).2] at e; cases e⟩,
    hh.keep hp ps hN fr (by simp only [VG.Proof.MlDsa.X86.Sign.nS]; omega) fun c hc => ⟨(hb c hc).1, fun e => by
      rw [(hb c hc).2] at e; cases e⟩,
    VG.Proof.MlDsa.X86.Sign.keepW' hp hN fr (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) fun c hc => ⟨(hb c hc).1, fun e => by
      rw [(hb c hc).2] at e; cases e⟩⟩

theorem sig_ok {o l : Nat} (h : o + l ≤ p.sigLen) (hl : 0 < l) : (VG.Proof.MlDsa.X86.Sign.Y p).okW (bSig o l) = true :=
  Lay.okW_iff.mpr ⟨Lay.ok_iff.mpr ⟨by rw [VG.Proof.MlDsa.X86.Sign.Y_n]; exact (by decide : 3 < 5), hl, by rw [VG.Proof.MlDsa.X86.Sign.Y_alen3]; exact h⟩, rfl⟩

/-- Before the signature, the last iteration `U s₀` having passed. -/
structure OI (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (U : State → Nat) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s
  fy : VG.Proof.MlDsa.X86.Sign.Fam s₀ s.mem (VG.Proof.MlDsa.X86.Sign.yB p) p.ℓ (VG.Proof.MlDsa.X86.Sign.Zv p s₀ (p.ℓ * U s₀))
  fh : VG.Proof.MlDsa.X86.Sign.HF s₀ s.mem p.k (VG.Proof.MlDsa.X86.Sign.Hv p s₀ (p.ℓ * U s₀))
  run : VG.Proof.MlDsa.X86.Sign.Run p F (U s₀) s₀
  ball : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * U s₀)) = true
  pass : VG.Proof.MlDsa.X86.Sign.passS p (U s₀) s₀
  ok1 : VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = 1
  ct : bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * U s₀)

/-- `c̃` to `sig`. -/
theorem outCopy_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (U : State → Nat) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.OI p F U) (VG.Proof.MlDsa.X86.Sign.OS p F U 0) (copyW SC (sc oCT (cLen p)) (bSig 0 (cLen p)) (cLen p / 4)) := by
  have hc := ps.hcLen
  have e4 : 4 * (cLen p / 4) = cLen p := by omega
  have e : copyW SC (sc oCT (cLen p)) (bSig 0 (cLen p)) (cLen p / 4) =
      copyW SC ⟨SC, oCT, 4 * (cLen p / 4)⟩ ⟨3, 0, 4 * (cLen p / 4)⟩ (cLen p / 4) := rfl
  rw [e]
  refine VG.Proof.MlDsa.X86.Sign.copy_piece SC oCT 3 0 (cLen p / 4) (by omega) (by omega) (by ofs) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h c' fr hb => ?_
  have fr' : Frame (FR s₀ [⟨3, 0, 4 * (cLen p / 4)⟩] 80) s.mem s'.mem := fr.mono (by simp)
  have hk := VG.Proof.MlDsa.X86.Sign.sigKeep hp ps h.fy h.fh (by decide) fr' fun c hc => by
    rw [List.mem_singleton] at hc; subst hc; exact ⟨by ofs, rfl⟩
  refine ⟨c', hk.1, hk.2.1, h.run, h.ball, h.pass, by rw [VG.Proof.MlDsa.X86.Sign.scw, hk.2.2]; exact h.ok1, ?_⟩
  rw [e4] at hb
  simp only [Nat.mul_zero, Nat.add_zero]
  rw [show VG.Proof.MlDsa.X86.Sign.zEnc p s₀ (p.ℓ * U s₀) 0 = [] from rfl, List.append_nil]
  exact hb.trans h.ct

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
theorem packZ_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (U : State → Nat) (r : Nat) (hr : r < p.ℓ) :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.OS p F U r) (VG.Proof.MlDsa.X86.Sign.OS p F U (r + 1)) (packZ P p r) := by
  have hz := ps.hzLen
  have hβ := ps.hβ
  have hm : zLen p * r + zLen p ≤ zLen p * p.ℓ := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  have hc := ps.hcLen
  refine VG.Proof.MlDsa.X86.Sign.bp_piece F.bitPack (F.ok _ (by simp)) (p.γ₁ - 1) p.γ₁ (zLen p) ps.hz.1 ps.hz.2 ⟨by omega, by omega, by omega⟩
    SC (VG.Impl.MlDsa.X86.Sign.oP (VG.Proof.MlDsa.X86.Sign.yB p + r)) 3 (sigZ p r) (by ofs) (fun s₀ s _ h => ⟨h.ctx, (VG.Proof.MlDsa.X86.Sign.fam_at h.fy hr).1,
      VG.Proof.MlDsa.X86.Sign.inRange_of_norm (VG.Proof.MlDsa.X86.Sign.fam_at h.fy hr) (h.pass.1 r hr) (by omega)⟩) fun s₀ s s' hp h c' fr hb => ?_
  have hk := VG.Proof.MlDsa.X86.Sign.sigKeep hp ps h.fy h.fh (by decide) fr fun c hc => by
    rw [List.mem_singleton] at hc; subst hc; exact ⟨by ofs, rfl⟩
  refine ⟨c', hk.1, hk.2.1, h.run, h.ball, h.pass, by rw [VG.Proof.MlDsa.X86.Sign.scw, hk.2.2]; exact h.ok1, ?_⟩
  rw [bytes_split hp s'.mem (o' := sigZ p r) (l₁ := cLen p + zLen p * r) (l₂ := zLen p) (by simp only [sigZ]; omega) (by rw [Nat.mul_succ]; omega)
    (by ofs) (by ofs), keepBytes hp (N := 80) (by show 80 + 16 ≤ 96; decide) (b := ⟨3, 0, cLen p + zLen p * r⟩) (by ofs) fr, h.sig, hb,
    (VG.Proof.MlDsa.X86.Sign.fam_at h.fy hr).2, List.append_assoc]
  simp only [VG.Proof.MlDsa.X86.Sign.zEnc, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The signature, of the last iteration `U s₀`. -/
abbrev sigV (p : Params) (s₀ : State) (κ : Nat) : List Byte :=
  VG.Proof.MlDsa.X86.Sign.CTv p s₀ κ ++ VG.Proof.MlDsa.X86.Sign.zEnc p s₀ κ p.ℓ ++ VG.Spec.MlDsa.hintBitPack p.ω p.k ((List.range p.k).map (VG.Proof.MlDsa.X86.Sign.Hv p s₀ κ))

/-- `HintBitPack(h)` to `sig`. -/
theorem hpack_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (U : State → Nat)
    (hU : ∀ s₀ s₀', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀' → VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀' → U s₀ = U s₀') :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.OS p F U p.ℓ) (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = 1 ∧
      bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen = VG.Proof.MlDsa.X86.Sign.sigV p s₀ (p.ℓ * U s₀))
      (hintBitPackAt P (sc (VG.Impl.MlDsa.X86.Sign.oP 5) (1024 * p.k)) p.ω (bSig (sigH p) (p.ω + p.k))) := by
  have hz := ps.hzLen
  have hc := ps.hcLen
  have hsl := ps.hsigLen
  unfold hintBitPackAt
  rw [show (sc (VG.Impl.MlDsa.X86.Sign.oP 5) (1024 * p.k)).len / 4 = 256 * p.k by show 1024 * p.k / 4 = _; omega]
  refine VG.Proof.MlDsa.X86.Sign.hbp_piece F.hintBitPack (F.ok _ (by simp)) p.ω p.k ps.hhint SC (VG.Impl.MlDsa.X86.Sign.oP 5) 3 (sigH p) (by ofs)
    (fun s₀ s hp h => ⟨h.ctx, ?_⟩) (fun s₀ s₀' s s' hp hp' hq h h' => ?_) fun s₀ s s' hp h c' fr hb =>
      ⟨c', by rw [VG.Proof.MlDsa.X86.Sign.scw, (VG.Proof.MlDsa.X86.Sign.sigKeep hp ps h.fy h.fh (by decide) fr fun c hc => by
        rw [List.mem_singleton] at hc; subst hc; exact ⟨by ofs, rfl⟩).2.2]; exact h.ok1, ?_⟩
  · rw [VG.Proof.MlDsa.X86.Sign.hintAt_of hp ps h.fh, VG.Proof.MlDsa.X86.Sign.hintOnes_map]; exact h.pass.2.2.2
  · rw [VG.Proof.MlDsa.X86.Sign.hint_list hp ps h.fh, VG.Proof.MlDsa.X86.Sign.hint_list hp' ps h'.fh, ← hU s₀ s₀' hp hp' hq]
    exact (((VG.Proof.MlDsa.X86.Sign.run_at ps hq h.run).2 h.ball).2 h.pass)
  · rw [bytes_split hp s'.mem (o' := sigH p) (l₁ := cLen p + zLen p * p.ℓ) (l₂ := p.ω + p.k) (by simp only [sigH]; omega)
      (by omega) (by ofs) (by ofs), keepBytes hp (N := 80) (by show 80 + 16 ≤ 96; decide)
      (b := ⟨3, 0, cLen p + zLen p * p.ℓ⟩) (by ofs) fr, h.sig, hb, VG.Proof.MlDsa.X86.Sign.hintAt_of hp ps h.fh]

/-- The signature. -/
theorem output_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (U : State → Nat)
    (hU : ∀ s₀ s₀', TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ → TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀' → VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀' → U s₀ = U s₀') :
    VG.Proof.MlDsa.X86.Sign.SP p (VG.Proof.MlDsa.X86.Sign.OI p F U) (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = 1 ∧
      bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen = VG.Proof.MlDsa.X86.Sign.sigV p s₀ (p.ℓ * U s₀)) (output P p) := by
  unfold output
  refine (VG.Proof.MlDsa.X86.Sign.outCopy_piece F ps U).seq (Piece.seq ?_ (VG.Proof.MlDsa.X86.Sign.hpack_piece F ps U hU))
  have := VG.Proof.MlDsa.X86.Sign.seqR_piece (p := p) (I := VG.Proof.MlDsa.X86.Sign.OS p F U) 0 p.ℓ fun r _ hr => VG.Proof.MlDsa.X86.Sign.packZ_piece F ps U r (by omega)
  simpa using this

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Final`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the body

After `ExpandA`, the rest (`rest_piece`: the private key, the loop, and the
signature if the last iteration passed) leaves `OK`, and `sig` if it is 1, as
`Sign_internal` says (`Outcome`, `rest_outcome`): 1 with the signature within
`maxBounds` if the last iteration passed, and 0 with `Sign_internal` failing
within `minBounds` if `SampleInBall` failed or the 814 iterations were
rejected; and 0 at once if an entry of `Â` failed (`body_piece`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only P0)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-! ## `Sign_internal` -/

section
variable {s₀ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : VG.Proof.MlDsa.X86.Sign.seedE p s₀ (p.ℓ * i + j) = aSeed (VG.Proof.MlDsa.X86.Sign.rhoS p s₀) i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [VG.Proof.MlDsa.X86.Sign.seedE, e1, e2]

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.X86.Sign.seedE p s₀ e) = none) :
    signMu p minBounds (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega
  exact signMu_none_A (VG.Proof.MlDsa.Sign.expandA_none ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (rhoV (VG.Proof.MlDsa.X86.Sign.skOf p s₀)) = some (amat p (Av (VG.Proof.MlDsa.X86.Sign.skOf p s₀))))
    (hL : loopV p (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) minBounds minBounds.sign 0 = none) :
    signMu p minBounds (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀) = none := by
  cases e : expandA p minBounds (rhoV (VG.Proof.MlDsa.X86.Sign.skOf p s₀)) with
  | none => exact signMu_none_A e
  | some A' =>
    have := VG.Proof.MlDsa.Sign.expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact signMu_none_L e hL

theorem sigOf_eq (κ : Nat) :
    sigOf p (VG.Proof.MlDsa.X86.Sign.CTv p s₀ κ, (List.range p.ℓ).map (VG.Proof.MlDsa.X86.Sign.Zv p s₀ κ), (List.range p.k).map (VG.Proof.MlDsa.X86.Sign.Hv p s₀ κ)) = VG.Proof.MlDsa.X86.Sign.sigV p s₀ κ := by
  simp only [sigOf, sigEncode, VG.Proof.MlDsa.X86.Sign.sigV, VG.Proof.MlDsa.X86.Sign.zEnc, List.flatMap_map, List.map_map]
  rfl

end

/-! ## The rest -/

/-- After the rest, the last iteration being `NI - 1`. -/
structure RD (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s
  run : VG.Proof.MlDsa.X86.Sign.Run p F (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1) s₀
  ok : VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = if (F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1))) && decide (VG.Proof.MlDsa.X86.Sign.passS p (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1) s₀))
    then 1 else 0
  sig : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1))) = true → VG.Proof.MlDsa.X86.Sign.passS p (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1) s₀ →
    bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen = VG.Proof.MlDsa.X86.Sign.sigV p s₀ (p.ℓ * (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1))
  none : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1))) = false →
    VG.Spec.MlDsa.sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1))) = none

/-- Whether the last iteration passed, in a run whose `Â` was sampled. -/
def lastB (p : Params) (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (s₀ : State) : Bool :=
  decide (VG.Proof.MlDsa.X86.Sign.Good p F s₀) && F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1))) &&
    decide (VG.Proof.MlDsa.X86.Sign.passS p (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1) s₀)

theorem lastB_eq {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} {s₀ s₀' : State} (ps : VG.Proof.MlDsa.X86.Sign.PS p) (hq : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀') : VG.Proof.MlDsa.X86.Sign.lastB p F s₀ = VG.Proof.MlDsa.X86.Sign.lastB p F s₀' := by
  unfold VG.Proof.MlDsa.X86.Sign.lastB
  by_cases h : VG.Proof.MlDsa.X86.Sign.Good p F s₀
  · have h' := (VG.Proof.MlDsa.X86.Sign.good_iff ps hq).mp h
    have hr : VG.Proof.MlDsa.X86.Sign.Run p F (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1) s₀ := ⟨h, by have := VG.Proof.MlDsa.X86.Sign.NI_pos (p := p) F s₀; omega⟩
    obtain ⟨ect, hb⟩ := VG.Proof.MlDsa.X86.Sign.run_at ps hq hr
    rw [← VG.Proof.MlDsa.X86.Sign.NI_eq ps hq, ← ect, decide_eq_true h, decide_eq_true h']
    cases e : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1)))
    · simp only [Bool.true_and, Bool.false_and]
    · simp only [Bool.true_and]
      exact decide_eq_decide.mpr (hb e).1
  · have h' : ¬ VG.Proof.MlDsa.X86.Sign.Good p F s₀' := fun h' => h ((VG.Proof.MlDsa.X86.Sign.good_iff ps hq).mpr h')
    rw [decide_eq_false h, decide_eq_false h', Bool.false_and, Bool.false_and, Bool.false_and, Bool.false_and]

/-- The private key, the loop, and the signature if the last iteration passed. -/
theorem rest_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => (∃ s', VG.Proof.MlDsa.X86.Sign.IA p F.rejF (p.k * p.ℓ) s₀ s' ∧ VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ s.mem = s'.mem) ∧
      VG.Proof.MlDsa.X86.Sign.okE p F.rejF s₀ (p.k * p.ℓ) = true) (VG.Proof.MlDsa.X86.Sign.RD p F) (rest P p) := by
  unfold rest
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Sign.KD p s₀ s ∧ VG.Proof.MlDsa.X86.Sign.Good p F s₀) ((VG.Proof.MlDsa.X86.Sign.sp_pure (VG.Proof.MlDsa.X86.Sign.Good p F) (VG.Proof.MlDsa.X86.Sign.decode_piece F ps)).mono
    (fun s₀ s _ h => ?_) fun _ _ _ h => h) ?_
  · obtain ⟨⟨s', ia, c, m⟩, hg⟩ := h
    exact ⟨⟨c, ⟨by rw [m]; exact ia.fam hg, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _)⟩⟩, hg⟩
  refine Piece.seq (VG.Proof.MlDsa.X86.Sign.signLoop_piece F ps) ?_
  refine VG.Proof.MlDsa.X86.Sign.okIte_piece (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (VG.Proof.MlDsa.X86.Sign.lastB p F) (fun s₀ s _ h => ⟨h.ctx, ?_⟩)
    (fun s₀ s₀' _ _ hq => VG.Proof.MlDsa.X86.Sign.lastB_eq ps hq) ?_ ?_
  · rw [h.ok]; simp only [VG.Proof.MlDsa.X86.Sign.lastB, decide_eq_true h.run.1, Bool.true_and]
  · let U : State → Nat := fun s₀ => VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1
    let φ : State → Prop := fun s₀ => VG.Proof.MlDsa.X86.Sign.Run p F (U s₀) s₀ ∧ F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * U s₀)) = true ∧
      VG.Proof.MlDsa.X86.Sign.passS p (U s₀) s₀
    refine ((VG.Proof.MlDsa.X86.Sign.sp_pure φ (VG.Proof.MlDsa.X86.Sign.output_piece F ps U fun s₀ s₀' _ _ hq => by
      simp only [U, VG.Proof.MlDsa.X86.Sign.NI_eq ps hq])).mono (fun s₀ s hp h => ?_) fun s₀ s _ h => ?_)
    · obtain ⟨⟨s', fn, c, m⟩, hb⟩ := h
      simp only [VG.Proof.MlDsa.X86.Sign.lastB, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨_, hs⟩, hq⟩ := hb
      obtain ⟨f1, f2, f3⟩ := fn.out hs hq
      refine ⟨⟨c, by rw [m]; exact f1, by rw [m]; exact f2, fn.run, hs, hq, ?_, by rw [m]; exact f3⟩, fn.run, hs, hq⟩
      rw [VG.Proof.MlDsa.X86.Sign.scw, m, ← VG.Proof.MlDsa.X86.Sign.scw, fn.ok, hs, decide_eq_true hq]; rfl
    · obtain ⟨⟨c, ok1, sg⟩, hr, hs, hq⟩ := h
      refine ⟨c, hr, by rw [ok1, hs, decide_eq_true hq]; rfl, fun _ _ => sg, fun e => by rw [hs] at e; cases e⟩
  · refine VG.Proof.MlDsa.X86.Sign.nil_piece fun s₀ s _ h => ?_
    obtain ⟨⟨s', fn, c, m⟩, hb⟩ := h
    refine ⟨c, fn.run, by rw [VG.Proof.MlDsa.X86.Sign.scw, m, ← VG.Proof.MlDsa.X86.Sign.scw]; exact fn.ok, fun hs hq => ?_, fn.none⟩
    simp only [VG.Proof.MlDsa.X86.Sign.lastB, decide_eq_true fn.run.1, hs, decide_eq_true hq] at hb
    cases hb

/-- What the rest leaves is `Sign_internal`'s outcome. -/
theorem rest_outcome {F : VG.Proof.MlDsa.X86.Sign.PrimsOk P} (ps : VG.Proof.MlDsa.X86.Sign.PS p) {s₀ s : State} (h : VG.Proof.MlDsa.X86.Sign.RD p F s₀ s) :
    Outcome (fun b => signMu p b (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀)) (VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK)
      (bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen) := by
  have hg := h.run.1
  have hA := VG.Proof.MlDsa.X86.Sign.expandA_good hg
  have hNI := VG.Proof.MlDsa.X86.Sign.NI_good hg
  have hpos := VG.Proof.MlDsa.X86.Sign.NI_pos (p := p) F s₀
  have hlt := h.run.lt
  have hc := h.run.cont
  cases hs : F.ballF p.τ (VG.Proof.MlDsa.X86.Sign.CTv p s₀ (p.ℓ * (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1)))
  · refine .inr ⟨by rw [h.ok, hs, Bool.false_and]; rfl, VG.Proof.MlDsa.X86.Sign.signMu_min_L hA ?_⟩
    exact loopV_none_ball ps.hok F.ballMax hc (h.none hs)
  · by_cases hq : VG.Proof.MlDsa.X86.Sign.passS p (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1) s₀
    · refine .inl ⟨by rw [h.ok, hs, decide_eq_true hq]; rfl, maxBounds, ?_⟩
      rw [h.sig hs hq, ← VG.Proof.MlDsa.X86.Sign.sigOf_eq]
      exact signMu_some hA (loopV_pass ps.hok F.ballMax (by show _ < 1000; omega) hc hs hq)
    · refine .inr ⟨by rw [h.ok, hs, decide_eq_false hq]; rfl, VG.Proof.MlDsa.X86.Sign.signMu_min_L hA ?_⟩
      have hcu : VG.Proof.MlDsa.X86.Sign.contS p F (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1) s₀ = true := by
        simp only [VG.Proof.MlDsa.X86.Sign.contS, contV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
        exact ⟨hs, hq⟩
      have hn : VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1 + 1 < VG.Proof.MlDsa.X86.Sign.NI p F s₀ ↔ VG.Proof.MlDsa.X86.Sign.contS p F (VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1) s₀ = true ∧ VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1 + 1 < 814 := by
        rw [hNI]; exact nIt_next _ (by have : VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1 < VG.Proof.MlDsa.X86.Sign.NI p F s₀ := by omega
                                       rw [hNI] at this; exact this)
      have hu : VG.Proof.MlDsa.X86.Sign.NI p F s₀ - 1 = 813 := by
        by_contra hne
        exact absurd (hn.mpr ⟨hcu, by omega⟩) (by omega)
      refine loopV_none_exh ps.hok F.ballMax fun j hj => ?_
      rcases (by omega : j < NI p F s₀ - 1 ∨ j = NI p F s₀ - 1) with hj' | rfl
      · exact hc j hj'
      · exact hcu

/-! ## The body -/

/-- What signing returns, and leaves in `sig`, from the initial state `s₀`. -/
def Done (p : Params) (s₀ s : State) : Prop :=
  Outcome (fun b => signMu p b (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀)) (s.gpr .eax)
    (bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen)

theorem ldsc_tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp (20 + 4 * SC)))])
    (VG.X86.taint.hintOf (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp (20 + 4 * SC)))]))).isSome = true := by
  taint_decide

/-- The body of `vg_mldsa*_sign`. -/
theorem body_piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => s = P0 s₀) (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.Done p s₀ s) (body P p) := by
  unfold body
  refine Piece.seq (VG.Proof.MlDsa.X86.Sign.lift (ldsc_piece (Y := VG.Proof.MlDsa.X86.Sign.Y p) (lk := VG.Proof.MlDsa.X86.Sign.lk0) VG.Proof.MlDsa.X86.Sign.ldsc_tt)) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK = 1)
    (VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h) (fun s₀ s hp h => ?_) rfl) ?_
  · rw [← List.append_nil (st32 oOK 1)]
    exact VG.Proof.MlDsa.X86.Sign.wp_st32 hp h (VG.Proof.MlDsa.X86.Sign.sc_ok ps (by decide) (by decide)) 1 fun s' c' _ v => WP.block_nil_iff.mpr ⟨c', v⟩
  refine Piece.seq (VG.Proof.MlDsa.X86.Sign.expandA_piece F ps) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ Outcome (fun b => signMu p b (VG.Proof.MlDsa.X86.Sign.skOf p s₀) (VG.Proof.MlDsa.X86.Sign.muOf s₀) (VG.Proof.MlDsa.X86.Sign.rndOf s₀))
      (VG.Proof.MlDsa.X86.Sign.scw s₀ s oOK) (bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen))
    (VG.Proof.MlDsa.X86.Sign.okIte_piece (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide)) (fun s₀ => VG.Proof.MlDsa.X86.Sign.okE p F.rejF s₀ (p.k * p.ℓ))
      (fun _ _ _ h => ⟨h.ctx, h.ok⟩) (fun _ _ _ _ hq => VG.Proof.MlDsa.X86.Sign.okE_eq ps hq _)
      ((VG.Proof.MlDsa.X86.Sign.rest_piece F ps).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, VG.Proof.MlDsa.X86.Sign.rest_outcome ps h⟩)
      (VG.Proof.MlDsa.X86.Sign.nil_piece fun s₀ s _ h => ?_)) ?_
  · obtain ⟨⟨s', ia, c, m⟩, hb⟩ := h
    refine ⟨c, .inr ⟨by rw [VG.Proof.MlDsa.X86.Sign.scw, m, ← VG.Proof.MlDsa.X86.Sign.scw, ia.ok, hb]; rfl, VG.Proof.MlDsa.X86.Sign.signMu_min_A (ia.bad hb)⟩⟩
  refine VG.Proof.MlDsa.X86.Sign.blk_piece (fun _ _ _ h => h.1) (fun s₀ s hp h => VG.Proof.MlDsa.X86.Sign.wp_ldsc hp h.1 (VG.Proof.MlDsa.X86.Sign.sc_ok' ps (by decide) (by decide))
    fun s' o' v' => WP.block_nil_iff.mpr ⟨h.1.only o' (by simp) (by simp), ?_⟩) rfl
  unfold VG.Proof.MlDsa.X86.Sign.Done
  rw [v', o'.mem]
  exact h.2

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Inst`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the primitives it calls

The verified x86 implementations of the primitives (`prims`), and what the
proofs of signing need of them (`prims_ok`): their contracts, with 16 bytes of
stack (56 for the samplers); that they never write `esp`; and, of the two
samplers whose result signing branches on, what they return, from their own
proofs (`Fin` of `RejNtt.lean` and `BallTop.lean`): 1 exactly when the loop
over the output they squeeze (1008 and 272 bytes) finishes, which is within
`maxBounds`.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The x86 implementations of the primitives. -/
def prims : Prims where
  ntt := Impl.MlDsa.X86.Arith.ntt
  invNtt := Impl.MlDsa.X86.Arith.nttInv
  mul := Impl.MlDsa.X86.Arith.mul
  mulAdd := Impl.MlDsa.X86.Arith.mulAdd
  add := Impl.MlDsa.X86.Arith.add
  sub := Impl.MlDsa.X86.Arith.sub
  rejNTT := Impl.MlDsa.X86.Sample.rejNTT
  expandMask := Impl.MlDsa.X86.Sample.expandMask
  ball := Impl.MlDsa.X86.Sample.sampleInBall
  highBits := Impl.MlDsa.X86.Round.highBits
  lowBits := Impl.MlDsa.X86.Round.lowBits
  normLt := Impl.MlDsa.X86.Round.normLt
  makeHint := Impl.MlDsa.X86.Round.makeHint
  simpleBitPack := Impl.MlDsa.X86.Pack.simpleBitPack
  bitPack := Impl.MlDsa.X86.Pack.bitPack
  bitUnpack := Impl.MlDsa.X86.Pack.bitUnpack
  hintBitPack := Impl.MlDsa.X86.Pack.hintBitPack

/-! ## The samplers' results -/

section
open VG.Proof.MlDsa.Sample VG.Proof.MlDsa.X86.Sample

/-- Whether `vg_mldsa_rej_ntt_poly` succeeds on a seed. -/
def rejF (B : List Byte) : Bool := decide ((rnFold [] (G B 1008)).length = 256)

/-- Whether `vg_mldsa_sample_in_ball` succeeds on `τ` and a seed. -/
def ballF (τ : Nat) (B : List Byte) : Bool := decide ((ballFold τ (H B 272)).2 = 256)

theorem rej_ret (s : State) (h : (rejNTTContract X86.abi 56).pre s) (t : List Leak) (s' : State)
    (e : Exec isa Impl.MlDsa.X86.Sample.rejNTT s t s') :
    s'.gpr .eax = if VG.Proof.MlDsa.X86.Sign.rejF (bytesAt s.mem ((arg s 0).setWidth 64) 34) then 1 else 0 := by
  obtain ⟨t', s'', e', hq⟩ := RejNtt.piece.wp s s (RejNtt.Pre.of h) rfl
  obtain ⟨-, rfl⟩ := Exec.det e e'
  obtain ⟨-, -, -, sf, hfin, -, hax⟩ := hq
  have hl := hfin.len
  have eL : RejNtt.LA (RejNtt.L.Msg s) 336 = rnFold [] (G (RejNtt.L.Msg s) 1008) := by
    simp only [RejNtt.LA]; rw [List.take_of_length_le (by rw [RejNtt.X_length])]
  rw [hax, hfin.eax, eL]
  rw [eL] at hl
  show _ = if decide ((rnFold [] (G (RejNtt.L.Msg s) 1008)).length = 256) = true then 1 else 0
  by_cases e : (rnFold [] (G (RejNtt.L.Msg s) 1008)).length = 256
  · rw [e, decide_eq_true rfl]; rfl
  · rw [Nat.div_eq_of_lt (by omega), decide_eq_false e]; rfl

theorem ball_ret (s : State) (h : (sampleInBallContract X86.abi 56).pre s) (t : List Leak) (s' : State)
    (e : Exec isa Impl.MlDsa.X86.Sample.sampleInBall s t s') :
    s'.gpr .eax = if VG.Proof.MlDsa.X86.Sign.ballF (arg s 2).toNat (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) then 1 else 0 := by
  obtain ⟨t', s'', e', hq⟩ := Ball.piece.wp s s (Ball.QPre.of h) rfl
  obtain ⟨-, rfl⟩ := Exec.det e e'
  obtain ⟨-, -, -, sf, hfin, -, hax⟩ := hq
  have hl : (Ball.S' s 264).2 ≤ 256 := Ball.st_le _ _ _
  rw [hax, hfin.eax]
  rw [Ball.S'_all] at hl ⊢
  show _ = if decide ((ballFold (Ball.τ s) (H (Ball.L.Msg s) 272)).2 = 256) = true then 1 else 0
  by_cases e : (ballFold (Ball.τ s) (H (Ball.L.Msg s) 272)).2 = 256
  · rw [e, decide_eq_true rfl]; rfl
  · rw [Nat.div_eq_of_lt (by omega), decide_eq_false e]; rfl

theorem rejMax (B : List Byte) (h : VG.Proof.MlDsa.X86.Sign.rejF B = true) : (rejNTTPoly maxBounds.rejNTT B).isSome := by
  simp only [VG.Proof.MlDsa.X86.Sign.rejF, decide_eq_true_eq] at h
  rw [VG.Proof.MlDsa.Sign.rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (rejNTT_some h)]; rfl

theorem ballMax : BallF VG.Proof.MlDsa.X86.Sign.ballF := fun τ B h => by
  simp only [VG.Proof.MlDsa.X86.Sign.ballF, decide_eq_true_eq] at h
  rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide) (sampleInBall_some τ (by decide) h)]; rfl

end

theorem cok {c : Prog isa} (h₁ : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) (h₂ : stackUse c ≤ 56) : VG.Proof.MlDsa.X86.Sign.COk c :=
  ⟨NoSp.of_all h₁, h₂⟩

/-- The primitives satisfy what the proofs of signing need of them. -/
def prims_ok : VG.Proof.MlDsa.X86.Sign.PrimsOk VG.Proof.MlDsa.X86.Sign.prims where
  ntt := Proof.MlDsa.X86.Arith.NttFwd.verified
  invNtt := Proof.MlDsa.X86.Arith.NttInvP.verified
  mul := Proof.MlDsa.X86.Arith.mul_verified
  mulAdd := Proof.MlDsa.X86.Arith.mulAdd_verified
  add := Proof.MlDsa.X86.Arith.add_verified
  sub := Proof.MlDsa.X86.Arith.sub_verified
  expandMask := Proof.MlDsa.X86.Sample.ExpandMask.verified
  highBits := Proof.MlDsa.X86.Round.highBits_verified
  lowBits := Proof.MlDsa.X86.Round.lowBits_verified
  normLt := Proof.MlDsa.X86.Round.normLt_verified
  makeHint := Proof.MlDsa.X86.Round.makeHint_verified
  simpleBitPack := Proof.MlDsa.X86.Pack.SimpleBitPack.verified
  bitPack := Proof.MlDsa.X86.Pack.BitPack.verified
  bitUnpack := Proof.MlDsa.X86.Pack.Unpack.BU.verified
  hintBitPack := Proof.MlDsa.X86.Pack.Hint.hintBitPack_verified
  rejF := VG.Proof.MlDsa.X86.Sign.rejF
  rejNTT := VG.Proof.MlDsa.X86.Sign.verified_withRet Proof.MlDsa.X86.Sample.RejNtt.verified VG.Proof.MlDsa.X86.Sign.rej_ret
  rejMax := VG.Proof.MlDsa.X86.Sign.rejMax
  ballF := VG.Proof.MlDsa.X86.Sign.ballF
  ball := VG.Proof.MlDsa.X86.Sign.verified_withRet Proof.MlDsa.X86.Sample.Ball.verified VG.Proof.MlDsa.X86.Sign.ball_ret
  ballMax := VG.Proof.MlDsa.X86.Sign.ballMax
  ok := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact VG.Proof.MlDsa.X86.Sign.cok (by decide +kernel) (by decide +kernel)

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Pre`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): the contract

The contract's precondition implies the layout `Y p` of the arguments
(`pre_of`); its public data are the pointers and `signLeak`, which is
`signLeakT` (`pub_of`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece E0 retR)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

set_option linter.unusedSimpArgs false in
theorem pre_of {s₀ : State} (h : (signContract p X86.abi 96).pre s₀) : TPre (VG.Proof.MlDsa.X86.Sign.Y p) s₀ := by
  sig_pre [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, d03, d04, d0g, d13, d14, d1g, d23, d24, d2g, d34, d3g, d4g, r0, r1, r2, r3, r4, rg,
    s0, s1, s2, s3, s4, sg, f0, f1, f2, f3, f4⟩ := h
  rw [Nat.mul_comm (scratchWords p) 8] at h4 d04 d14 d24 d34 d4g r4 s4 f4
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [VG.X86.Taint.sub_setWidth h1]
  rw [hs] at s0 s1 s2 s3 s4 sg
  have c5 : ∀ i, i < (VG.Proof.MlDsa.X86.Sign.Y p).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    rw [VG.Proof.MlDsa.X86.Sign.Y_n] at hi; omega
  refine ⟨h1, by show 16 ≤ 96; decide, by rw [VG.Proof.MlDsa.X86.Sign.Y_n]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sg, ?_, by show 4 < 5; decide⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    all_goals exact absurd hw (by simp [VG.Proof.MlDsa.X86.Sign.Y_awr0, VG.Proof.MlDsa.X86.Sign.Y_awr1, VG.Proof.MlDsa.X86.Sign.Y_awr2, VG.Proof.MlDsa.X86.Sign.Y_awr3, VG.Proof.MlDsa.X86.Sign.Y_awr4])
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by simp [VG.Proof.MlDsa.X86.Sign.Y_awr0, VG.Proof.MlDsa.X86.Sign.Y_awr1, VG.Proof.MlDsa.X86.Sign.Y_awr2, VG.Proof.MlDsa.X86.Sign.Y_awr3, VG.Proof.MlDsa.X86.Sign.Y_awr4])
    · exact absurd hw (by simp [VG.Proof.MlDsa.X86.Sign.Y_awr0, VG.Proof.MlDsa.X86.Sign.Y_awr1, VG.Proof.MlDsa.X86.Sign.Y_awr2, VG.Proof.MlDsa.X86.Sign.Y_awr3, VG.Proof.MlDsa.X86.Sign.Y_awr4])
    · exact absurd hw (by simp [VG.Proof.MlDsa.X86.Sign.Y_awr0, VG.Proof.MlDsa.X86.Sign.Y_awr1, VG.Proof.MlDsa.X86.Sign.Y_awr2, VG.Proof.MlDsa.X86.Sign.Y_awr3, VG.Proof.MlDsa.X86.Sign.Y_awr4])
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [h4]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by simp [VG.Proof.MlDsa.X86.Sign.Y_awr0, VG.Proof.MlDsa.X86.Sign.Y_awr1, VG.Proof.MlDsa.X86.Sign.Y_awr2, VG.Proof.MlDsa.X86.Sign.Y_awr3, VG.Proof.MlDsa.X86.Sign.Y_awr4]), absurd hw (by simp [VG.Proof.MlDsa.X86.Sign.Y_awr0, VG.Proof.MlDsa.X86.Sign.Y_awr1, VG.Proof.MlDsa.X86.Sign.Y_awr2, VG.Proof.MlDsa.X86.Sign.Y_awr3, VG.Proof.MlDsa.X86.Sign.Y_awr4]), d03, d04, absurd hw (by simp [VG.Proof.MlDsa.X86.Sign.Y_awr0, VG.Proof.MlDsa.X86.Sign.Y_awr1, VG.Proof.MlDsa.X86.Sign.Y_awr2, VG.Proof.MlDsa.X86.Sign.Y_awr3, VG.Proof.MlDsa.X86.Sign.Y_awr4]), absurd rfl hne, absurd hw (by simp [VG.Proof.MlDsa.X86.Sign.Y_awr0, VG.Proof.MlDsa.X86.Sign.Y_awr1, VG.Proof.MlDsa.X86.Sign.Y_awr2, VG.Proof.MlDsa.X86.Sign.Y_awr3, VG.Proof.MlDsa.X86.Sign.Y_awr4]), d13, d14, absurd hw (by simp [VG.Proof.MlDsa.X86.Sign.Y_awr0, VG.Proof.MlDsa.X86.Sign.Y_awr1, VG.Proof.MlDsa.X86.Sign.Y_awr2, VG.Proof.MlDsa.X86.Sign.Y_awr3, VG.Proof.MlDsa.X86.Sign.Y_awr4]), absurd hw (by simp [VG.Proof.MlDsa.X86.Sign.Y_awr0, VG.Proof.MlDsa.X86.Sign.Y_awr1, VG.Proof.MlDsa.X86.Sign.Y_awr2, VG.Proof.MlDsa.X86.Sign.Y_awr3, VG.Proof.MlDsa.X86.Sign.Y_awr4]), absurd rfl hne, d23, d24, d03.symm, d13.symm, d23.symm, absurd rfl hne, d34, d04.symm, d14.symm, d24.symm, d34.symm, absurd rfl hne]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [d0g.symm, d1g.symm, d2g.symm, d3g.symm, d4g.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [r0, r1, r2, r3, r4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [s0, s1, s2, s3, s4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [f0, f1, f2, f3, f4]

theorem addr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

theorem pub_of {s₀ s₀' : State} (h : (signContract p X86.abi 96).pub s₀ s₀') : VG.Proof.MlDsa.X86.Sign.SPub p s₀ s₀' := by
  sig_pub [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4⟩ := h
  refine ⟨⟨e₁, fun i hi => ?_, rfl⟩, ?_⟩
  · rw [VG.Proof.MlDsa.X86.Sign.Y_n] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    exacts [a0, a1, a2, a3, a4]
  · simp only [VG.Proof.MlDsa.X86.Sign.skOf, VG.Proof.MlDsa.X86.Sign.muOf, VG.Proof.MlDsa.X86.Sign.rndOf, bSk, bMu, bRnd, VG.Proof.MlDsa.X86.Sign.addr0, signLeakT_eq_signLeak]
    exact e₂

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Top`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): `vg_mldsa{44,65,87}_sign`

The body in the leaf's frame (`piece`), and `Verified` against `signContract`
(`verified`), for any implementations of the primitives that `PrimsOk` says
are verified, and any of the three parameter sets.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece P0 LeafPost satState)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-- A top-level function, from its body, for runs related by `SPub`. -/
theorem topLeafS {body : Prog isa} {B : State → State → Prop} (hsp : NoSp body)
    (hb : VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => s = P0 s₀) (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.Sign.Y p) s₀ s ∧ B s₀ s) body) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (B s₀) s₀ s') (Impl.MlKem.X86.leaf body) :=
  Piece.leaf (VG.Proof.MlKem.X86.Top.W (VG.Proof.MlDsa.X86.Sign.Y p)) hsp (fun _ hp => ⟨hp.E0_big, by have := hp.sp'; omega⟩) (fun _ hp => hp.hW)
    (fun _ _ _ _ hq => hq.1.1) (hb.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h.2⟩)

theorem piece (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (hsp : NoSp (body P p)) :
    VG.Proof.MlDsa.X86.Sign.SP p (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlDsa.X86.Sign.Done p s₀) s₀ s') (sign P p) :=
  VG.Proof.MlDsa.X86.Sign.topLeafS hsp (VG.Proof.MlDsa.X86.Sign.body_piece F ps)

/-- Memory with the arguments `0`, `0x2000`, `0x3000`, `0x8000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x500d then 0x30 else if a = 0x5011 then 0x80 else if a = 0x5016 then 1 else 0

theorem sat (h3 : VG.Proof.MlDsa.X86.Sign.Ok3 p) : ∃ s, (signContract p X86.abi 96).pre s := by
  rcases h3 with rfl | rfl | rfl
  · refine ⟨VG.Proof.MlKem.X86.satState VG.Proof.MlDsa.X86.Sign.satMem [⟨0, 2560⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 2420⟩, ⟨0x10000, 77824⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  · refine ⟨VG.Proof.MlKem.X86.satState VG.Proof.MlDsa.X86.Sign.satMem [⟨0, 4032⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 3309⟩, ⟨0x10000, 103424⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  · refine ⟨VG.Proof.MlKem.X86.satState VG.Proof.MlDsa.X86.Sign.satMem [⟨0, 4896⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 4627⟩, ⟨0x10000, 144384⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

/-- `vg_mldsa{44,65,87}_sign`, with the primitives `P`, is verified against `signContract`. -/
theorem verified (F : VG.Proof.MlDsa.X86.Sign.PrimsOk P) (h3 : VG.Proof.MlDsa.X86.Sign.Ok3 p) (hsp : NoSp (body P p)) :
    Verified X86.target (sign P p) (signContract p X86.abi 96) := by
  have ps := PS.of h3
  refine Piece.verified (((VG.Proof.MlDsa.X86.Sign.piece F ps hsp).pre_mono (fun _ h => VG.Proof.MlDsa.X86.Sign.pre_of h) fun _ _ _ _ h => VG.Proof.MlDsa.X86.Sign.pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) (VG.Proof.MlDsa.X86.Sign.sat h3)
  obtain ⟨habi, -, -, s, hd, hm, hax⟩ := hq
  refine ⟨habi, ?_⟩
  sig_post [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  rw [VG.Proof.MlDsa.X86.Sign.sw32, hax, hm]
  unfold VG.Proof.MlDsa.X86.Sign.Done at hd
  simp only [VG.Proof.MlDsa.X86.Sign.skOf, VG.Proof.MlDsa.X86.Sign.muOf, VG.Proof.MlDsa.X86.Sign.rndOf, bSk, bMu, bRnd, bSig, VG.Proof.MlDsa.X86.Sign.addr0] at hd
  exact hd

end VG.Proof.MlDsa.X86.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified`. -/
section

/-!
# ML-DSA signing on x86 (32-bit): verified

`vg_mldsa{44,65,87}_sign` (`sign prims p`) with the x86 primitives, verified
against `signContract` (`verified`, with `prims_ok`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlDsa.X86.Sign
open VG.Spec.MlDsa

theorem sign44_verified : Verified X86.target (sign VG.Proof.MlDsa.X86.Sign.prims mlDsa44) (signContract mlDsa44 X86.abi 96) :=
  VG.Proof.MlDsa.X86.Sign.verified VG.Proof.MlDsa.X86.Sign.prims_ok (.inl rfl) (NoSp.of_all (by decide +kernel))

theorem sign65_verified : Verified X86.target (sign VG.Proof.MlDsa.X86.Sign.prims mlDsa65) (signContract mlDsa65 X86.abi 96) :=
  VG.Proof.MlDsa.X86.Sign.verified VG.Proof.MlDsa.X86.Sign.prims_ok (.inr (.inl rfl)) (NoSp.of_all (by decide +kernel))

theorem sign87_verified : Verified X86.target (sign VG.Proof.MlDsa.X86.Sign.prims mlDsa87) (signContract mlDsa87 X86.abi 96) :=
  VG.Proof.MlDsa.X86.Sign.verified VG.Proof.MlDsa.X86.Sign.prims_ok (.inr (.inr rfl)) (NoSp.of_all (by decide +kernel))

end VG.Proof.MlDsa.X86.Sign

end
