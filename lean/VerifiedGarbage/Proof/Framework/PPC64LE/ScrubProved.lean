module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubWiped
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.CodeWalk
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# The cleanup's theorems (PPC64LE)

The theorems a registration binds (`verified := …`), about a
function's code as emitted: its body, then its cleanup
(`Impl.Scrub.PPC64LE.scrubAll rb d cl`).

* `verifiedScrubbedAll` covers code whose frames use `d` bytes of stack.
* `verifiedScrubbedWiped` covers code that wipes its own frame (`d = 0`).

The bytes of stack the cleanup wipes and the registers it clears are
literals in `Impl/`. What the cleanup needs of the code is one Boolean
(`scrubSide`, `wipedSide`), which the proof module gives by `lit_decide`, so
the kernel checks it when that module is built.
-/

@[expose] public section

open VG.Impl.Scrub.PPC64LE VG.Impl.StackScratch.PPC64LE

namespace VG.PPC64LE.Scrub

instance : RegIdx VReg := ⟨VReg.ctorIdx, fun {a b} h => by
  rw [← VReg.ofNat_ctorIdx a, h, VReg.ofNat_ctorIdx]⟩

/-- `Clear.WF`, as a Boolean. -/
def wfB (cl : Clear) (cs : List Nat) : Bool :=
  ((cs.isEmpty && !cl.ca) || cl.r0) && (cs.isEmpty || cl.gs.contains .r12) &&
    cl.gs.all scratchRegs.contains

theorem wf_of_wfB {cl : Clear} {cs : List Nat} (h : wfB cl cs = true) : cl.WF cs := by
  simp only [wfB, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_true',
    List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨h0, h12⟩, hg⟩ := h
  refine ⟨fun hc => ?_, fun hc => ?_, hg⟩
  · rcases h0 with ⟨he, hca⟩ | h0
    · rcases hc with hc | hc
      · exact absurd he hc
      · rw [hca] at hc; cases hc
    · exact h0
  · rcases h12 with he | h12
    · exact absurd he hc
    · exact h12

/-- The general-purpose registers the tail leaves as the code left them: the
volatile ones `cl` does not zero, and `r3` unless `cl.r3`. -/
def keptG (cl : Clear) : List Reg :=
  ((Reg.r0 :: scratchRegs).filter fun r => !((r == .r0 && cl.r0) || cl.gs.contains r)) ++
    (if cl.r3 then [] else [.r3])

/-- The vector registers the tail leaves as the code left them. -/
def keptV (cl : Clear) : List VReg := vregs.filter fun v => !cl.vs.contains v

/-- `VOp.dst`, with its cases closed (`inline_match%`). -/
def vopDstK : VOp → VReg := inline_match% VG.PPC64LE.VOp.dst

theorem vopDstK_eq (op : VOp) : vopDstK op = op.dst := by cases op <;> rfl

/-- `sideI`, the instruction first: one match. -/
def sideFn : Instr → RegSet Reg → RegSet VReg → Bool → Bool
  | .addc d .. | .adde d .. | .addze d _ | .subc d .. | .sube d .. => fun g _ ca => !g.mem d && ca
  | .vop op => fun _ v _ => !v.mem (vopDstK op)
  | .lxvd2x d .. | .lxvd2xTbl d .. | .mtvsrd d _ => fun _ v _ => !v.mem d
  | i => match dstOf i with
    | some d => fun g _ _ => !g.mem d
    | none => fun _ _ _ => true

/-- `sideFn`, with its cases closed (`inline_match%`). -/
def sideFnK : Instr → RegSet Reg → RegSet VReg → Bool → Bool :=
  inline_match% VG.PPC64LE.Scrub.sideFn VG.PPC64LE.dstOf

/-- Instruction `i` writes none of the registers `g` and `v`, nor CA unless
`ca` (`sideI_eq`). The kernel evaluates it at every instruction of the code:
it is one match, with its cases closed. -/
def sideI (g : RegSet Reg) (v : RegSet VReg) (ca : Bool) (i : Instr) : Bool := sideFnK i g v ca

theorem sideI_eq (g : RegSet Reg) (v : RegSet VReg) (ca : Bool) (i : Instr) : sideI g v ca i =
    ((match dstOf i with
      | none => true
      | some r => !g.mem r) &&
    (match vdstOf i with
      | none => true
      | some w => !v.mem w) &&
    (ca || !writesCa i)) := by
  cases i <;> first
    | (rename_i op; show (!v.mem (vopDstK op)) = _; rw [vopDstK_eq]; cases ca <;> simp [dstOf, vdstOf, writesCa])
    | (cases ca <;> simp [sideI, sideFnK, dstOf, vdstOf, writesCa])

/-- `writesCa`, with its cases closed (`inline_match%`). -/
def writesCaK : Instr → Bool := inline_match% VG.PPC64LE.writesCa

theorem writesCaK_eq (i : Instr) : writesCaK i = writesCa i := by cases i <;> rfl

/-! ## The checks the kernel evaluates (`CodeWalk`) -/

theorem inames_walk (c : Prog isa) : CodeWalk.inames c = inames c := by
  induction c with
  | block => rfl
  | seq a b iha ihb | ite _ a b iha ihb => rw [CodeWalk.inames, inames, iha, ihb]
  | loop b _ ih | call _ b ih | frame _ b _ ih => exact ih
  | icall _ _ a b iha ihb => rw [CodeWalk.inames, inames, iha, ihb]

theorem icallFree_of_namesIn {c : Prog isa} (h : CodeWalk.namesIn [] c = true) : icallFree c = true := by
  have hn : inames c = [] := by
    rw [← inames_walk]
    exact List.eq_nil_iff_forall_not_mem.mpr fun f hf => nomatch CodeWalk.namesIn_iff.mp h f hf
  clear h
  induction c with
  | block => rfl
  | seq a b iha ihb | ite _ a b iha ihb =>
    rw [inames, List.append_eq_nil_iff] at hn
    rw [icallFree, iha hn.1, ihb hn.2, Bool.and_self]
  | loop b _ ih | call _ b ih | frame _ b _ ih => exact ih hn
  | icall i n b nx => cases hn

/-- `c.ppc64leDepth`. Only the kernel evaluates it. -/
noncomputable def depthK (c : Prog isa) : Nat := CodeWalk.depth frameBytes 0 c

theorem depthK_eq (c : Prog isa) : depthK c = c.ppc64leDepth := by
  unfold depthK
  induction c with
  | block => rfl
  | seq a b iha ihb => rw [CodeWalk.depth_seq, Code.ppc64leDepth, iha, ihb]
  | ite _ a b iha ihb => rw [CodeWalk.depth_ite, Code.ppc64leDepth, iha, ihb]
  | icall _ _ a b iha ihb => rw [CodeWalk.depth_icall, Code.ppc64leDepth, iha, ihb, Nat.add_zero]
  | loop b _ ih => exact ih
  | call _ b ih => exact ih
  | frame i b _ ih => rw [CodeWalk.depth_frame, Code.ppc64leDepth, ih]

/-- Code `c` (callees included) writes no register the tail with `cl` leaves
as it is, the link registers among them if `c` calls: `Clear.Keeps`, as one
pass over the instructions with the registers as bit masks (`RegSet`); and it
calls indirectly only functions of `N`. Only the kernel evaluates it
(`Code.allInstrs`). When the tail clears every register, only writes to CA can
matter. -/
noncomputable def keepsB (c : Prog isa) (cl : Clear) (N : List String) : Bool :=
  if keptG cl = [] ∧ keptV cl = [] then
    Bool.rec (CodeWalk.sideAll (fun i => !writesCaK i) N c) (CodeWalk.namesIn N c) cl.ca
  else
    CodeWalk.sideAll (sideI (RegSet.ofList (keptG cl)) (RegSet.ofList (keptV cl)) cl.ca) N c &&
      (callFree c || linkRegs.all fun r => !(keptG cl).contains r)

private theorem keepsB_eq (c : Prog isa) (cl : Clear) (N : List String) : keepsB c cl N =
    ((c.allInstrs (sideI (RegSet.ofList (keptG cl)) (RegSet.ofList (keptV cl)) cl.ca) &&
      (inames c).all fun f => decide (f ∈ N)) &&
      (callFree c || linkRegs.all fun r => !(keptG cl).contains r)) := by
  unfold keepsB
  split
  · rename_i h
    obtain ⟨hg, hv⟩ := h
    rw [hg, hv]
    have empty : sideI (RegSet.ofList ([] : List Reg)) (RegSet.ofList ([] : List VReg)) cl.ca =
        fun i => cl.ca || !writesCa i := by
      funext i
      cases hd : dstOf i <;> cases hvec : vdstOf i <;>
        simp [sideI_eq, hd, hvec, RegSet.ofList, RegSet.mem, RegSet.empty]
    rw [empty]
    cases cl.ca
    · rw [show (Bool.rec (CodeWalk.sideAll (fun i => !writesCaK i) N c) (CodeWalk.namesIn N c) false : Bool) =
        CodeWalk.sideAll (fun i => !writesCaK i) N c from rfl, CodeWalk.sideAll_eq, inames_walk]
      simp [Code.allInstrs_eq, linkRegs, writesCaK_eq]
    · rw [show (Bool.rec (CodeWalk.sideAll (fun i => !writesCaK i) N c) (CodeWalk.namesIn N c) true : Bool) =
        CodeWalk.namesIn N c from rfl, CodeWalk.namesIn_eq, inames_walk]
      simp [Code.allInstrs_eq, linkRegs]
  · rw [CodeWalk.sideAll_eq, inames_walk]

theorem keeps_of_keepsB {c : Prog isa} {cl : Clear} {N : List String} (h : keepsB c cl N = true) : cl.Keeps c := by
  simp only [keepsB_eq, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hi, -⟩, hl⟩ := h
  have hall : ∀ i ∈ instrs c, (∀ r ∈ keptG cl, dstOf i ≠ some r) ∧ (∀ w ∈ keptV cl, vdstOf i ≠ some w) ∧
      (cl.ca = false → writesCa i = false) := by
    intro i hi'
    have h1 := List.all_eq_true.mp ((Code.allInstrs_eq _ c).symm.trans hi) i hi'
    simp only [sideI_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h1
    obtain ⟨⟨hg, hv⟩, hca⟩ := h1
    refine ⟨fun r hr he => ?_, fun w hw he => ?_, fun hc => ?_⟩
    · rw [he] at hg
      have hm : (RegSet.ofList (keptG cl)).mem r = true := RegSet.mem_ofList.mpr hr
      dsimp only at hg
      rw [hm] at hg; cases hg
    · rw [he] at hv
      have hm : (RegSet.ofList (keptV cl)).mem w = true := RegSet.mem_ofList.mpr hw
      dsimp only at hv
      rw [hm] at hv; cases hv
    · rcases hca with hca | hca
      · rw [hc] at hca; cases hca
      · exact hca
  have hlink : ∀ r ∈ keptG cl, callFree c = true ∨ r ∉ linkRegs := by
    intro r hr
    rcases hl with hl | hl
    · exact .inl hl
    · refine .inr fun hrl => ?_
      have := List.all_eq_true.mp hl r hrl
      rw [Bool.not_eq_true'] at this
      exact absurd (List.contains_iff_mem.mpr hr) (by rw [this]; exact Bool.false_ne_true)
  have hgk : ∀ r ∈ keptG cl, ∀ s t u, Exec isa c s t u → u.gpr r = s.gpr r := fun r hr s t u e =>
    Exec.gpr_of (fun i hi' => (hall i hi').1 r hr) e (hlink r hr)
  intro s t u he
  refine ⟨fun r h3 hv hz => hgk r (List.mem_append_left _ (List.mem_filter.mpr ⟨?_, ?_⟩)) s t u he,
    fun h3 => hgk .r3 (List.mem_append_right _ (by rw [h3]; exact List.mem_singleton.mpr rfl)) s t u he,
    fun v hv => (Exec.vpr_ca he).1 v fun i hi' => (hall i hi').2.1 v (List.mem_filter.mpr ⟨?_, ?_⟩),
    fun hc => (Exec.vpr_ca he).2 fun i hi' => (hall i hi').2.2 hc⟩
  · rcases hv with rfl | hv
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hv
  · rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hc
    rw [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hc
    exact hz hc
  · cases v <;> simp [vregs]
  · simpa using hv

theorem inames_of_keepsB {c : Prog isa} {cl : Clear} {N : List String} (h : keepsB c cl N = true) :
    ∀ n ∈ inames c, n ∈ N := by
  simp only [keepsB_eq, Bool.and_eq_true] at h
  exact fun n hn => of_decide_eq_true (List.all_eq_true.mp h.1.2 n hn)

/-- `Verified.scrubAll`, with the registers the tail clears given: any `cl`
that is well-formed for the levels and that the code keeps. The functions
the code calls indirectly have the same addresses in two runs that agree on
what is public (`hsy`). -/
theorem Verified.scrubWith {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa} {cl : Clear}
    (hA : ScrubAbi A) (h : Verified target c (sig.contract A pre post wa stack leak))
    (hd : c.ppc64leDepth ≤ stack) (h16 : c.ppc64leDepth % 16 = 0)
    (h48 : c.ppc64leDepth = 0 ∨ 48 ≤ c.ppc64leDepth)
    (hsy : ∀ s₁ s₂, (sig.contract A pre post wa stack leak).pub s₁ s₂ →
      ∀ n ∈ inames c, s₁.syms n = s₂.syms n) (hrb : sig.retBits A.ptrBits ≤ 64)
    (hpost : PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits))
    (hwf : cl.WF (chunks c.ppc64leDepth)) (hk : cl.Keeps c) :
    Verified target (Impl.Scrub.PPC64LE.scrubAll (sig.retBits A.ptrBits) c.ppc64leDepth cl c)
        (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.PPC64LE.scrubAll (sig.retBits A.ptrBits) c.ppc64leDepth cl c)
        (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  have hsum := chunks_sum h16
  refine Verified.scrubOf hA h (chunks_ok h16 h48) (by rw [hsum]; exact hd) hwf hk hrb hpost ?_
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hun a₁ a₂
  have hD₁ : c.ppc64leDepth ≤ s₁.sp.toNat := by
    rcases (contract_pre_scrub hA h₁).1 with h0 | h0
    · omega_using [h0, hd]
    · omega_using [h0, hd]
  have hL : (s₁.sp - BitVec.ofNat 64 c.ppc64leDepth).toNat = s₁.sp.toNat - c.ppc64leDepth :=
    toNat_sub_ofNat _ _ hD₁
  obtain ⟨-, hwr, -, -, -, -, hsp, -, hm⟩ := ho
  obtain ⟨-, hU, hA'⟩ := Exec.agreeS (R := s₁.rd ++ s₁.wr) (L := s₁.sp - BitVec.ofNat 64 c.ppc64leDepth)
    (T := s₁.sp) a₁ [] [] a₂ (hsy _ _ hp) hsp hwr hun (fun r hr => .inl (List.mem_append_right _ hr))
    (by rw [hL]; omega_using [hD₁]) (Nat.le_refl _) (fun x hx _ => hm x hx)
    (by rw [List.append_nil, List.append_nil]; exact (h.2.1) _ _ _ _ _ _ h₁ h₂ hp a₁ a₂)
  refine ⟨hU, fun x hx hc => hA' x hx fun hz => hc ?_⟩
  simp only [Cover, hsum]; simp only [InZ, hL] at hz; exact hz

/-- What `verifiedScrubbedAll` needs of code `c` run by `scrubAll rb d cl`,
with the tables `ts` (none by default): conditions on its frames (which use
`d` bytes) and its calls (indirectly, only of functions of `ts`:
`tableFns`, which with no table is that it makes no indirect call), that
the result has at most 64 bits, and that `cl` is a `Clear` the tail can run
that has every volatile register `c` may write. -/
noncomputable def scrubSide (c : Prog isa) (d rb : Nat) (cl : Clear)
    (ts : List (String × List FnTable) := []) : Bool :=
  Nat.beq (depthK c) d && d % 16 == 0 && (d == 0 || decide (48 ≤ d)) &&
    decide (rb ≤ 64) && wfB cl (chunks d) && keepsB c cl (tableFns ts) && (cl.r3 || rb != 32)

/-- `r`'s code, scrubbed with the stack and the registers stated, is
verified against `r`'s contract and returns without secret residue. -/
private theorem scrubAll_ok {api : Api} (r : Unscrubbed api target) {d : Nat} {cl : Clear}
    (hs : scrubSide r.code d (retBitsOf r) cl r.tables = true) (hd : d ≤ r.stack)
    (hpost : PostOut r.contract (retBitsOf r)) :
    Verified target (scrubAll (retBitsOf r) d cl r.code) r.contract ∧
      NoResidue (scrubAll (retBitsOf r) d cl r.code) r.contract (retBitsOf r) := by
  simp only [scrubSide, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, depthK_eq, Nat.beq_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨hde, h16⟩, h48⟩, hrb⟩, hwf⟩, hk⟩, -⟩ := hs
  subst hde
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  unfold retBitsOf at hrb hp ⊢
  rw [e] at hv hp ⊢
  have hrb' := hrb
  refine Verified.scrubWith (ScrubAbi.of r.consts api.sig r.tables) hv hd h16 h48
    (fun s₁ s₂ hp n hn => tables_pub_syms (contract_pub hp) n ?_) hrb' hp
    (wf_of_wfB hwf) (keeps_of_keepsB hk)
  exact inames_of_keepsB hk n hn

/-- What `verifiedScrubbedWiped` needs of code `c` that is
`withStackScratchWiped bytes reg words body`: that the frame is one
`withStackScratchWiped` can push, that its wipe covers the frame's region
and the body has no frames and makes no indirect call, that the result has at most 64 bits,
and that `cl` is a `Clear` the tail can run, with no stack to wipe, that has
every volatile register `c` may write. -/
noncomputable def wipedSide (c body : Prog isa) (bytes words rb : Nat) (cl : Clear) : Bool :=
  decide (32 < bytes) && decide (bytes < 4096) && bytes % 16 == 0 && 8 * words == bytes - 32 &&
    CodeWalk.namesIn [] body && Nat.beq (depthK body) 0 && decide (rb ≤ 64) && wfB cl [] && keepsB c cl [] &&
    (cl.r3 || rb != 32)

/-- `r`'s code, followed by the clearing of the registers stated alone, is
verified against `r`'s contract and returns without secret residue. -/
private theorem scrubWiped_ok {api : Api} (r : Unscrubbed api target) {bytes : Nat} {reg : Reg} {words : Nat}
    {body : Prog isa} {cl : Clear} (hc : r.code = withStackScratchWiped bytes reg words body)
    (hs : wipedSide r.code body bytes words (retBitsOf r) cl = true) (hst : bytes ≤ r.stack)
    (hpost : PostOut r.contract (retBitsOf r)) :
    Verified target (.seq r.code (scrubTail (retBitsOf r) [] cl)) r.contract ∧
      NoResidue (.seq r.code (scrubTail (retBitsOf r) [] cl)) r.contract (retBitsOf r) := by
  simp only [wipedSide, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, depthK_eq, Nat.beq_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hB1, hB2⟩, hB3⟩, hw⟩, hic⟩, hd⟩, hrb⟩, hwf⟩, hk⟩, -⟩ := hs
  have hic := icallFree_of_namesIn hic
  have sh : WipedShape r.code r.stack := ⟨bytes, reg, words, body, hc, ⟨hB1, hB2, hB3⟩, hw, hic, hd, hst⟩
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  unfold retBitsOf at hrb hp ⊢
  rw [e] at hv hp ⊢
  have hrb' := hrb
  have hA := ScrubAbi.of r.consts api.sig r.tables
  exact Verified.scrubOf hA hv ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩ (Nat.zero_le _)
    (wf_of_wfB hwf) (keeps_of_keepsB hk) hrb' hp (WipedShape.agree hA hv sh)

/-- `r`'s code, then the clearing of `cs` and of the registers `cl`, which fixes `r3`
wherever the result has 32 bits, returns its result as ELFv2 requires. -/
private theorem retAbi_scrub {api : Api} (r : Unscrubbed api target) {cs : List Nat} {cl : Clear}
    (hcl : (cl.r3 || retBitsOf r != 32) = true) (hgs : ∀ g ∈ cl.gs, g ∈ scratchRegs) :
    RetAbi target (.seq r.code (scrubTail (retBitsOf r) cs cl)) r.contract := by
  refine retAbi_of_fixA (rb := retBitsOf r) (fun f hf => ?_) (fun h32 s t s' _ he => ?_)
  · obtain ⟨pre, post, leak, e⟩ := r.ofSig
    rw [e] at hf
    exact retBits_of_retExt (ScrubAbi.of r.consts api.sig r.tables) hf
  · have hc : cl.r3 = true := by simpa [h32] using hcl
    cases he with | seq _ ht =>
    exact scrubTail_r3 hc (fun h => absurd (hgs _ h) (by decide)) ht

/-! ## The theorems a registration binds

`rb` is an argument, so that the hypotheses are stated with it and not with
a projection of `r`; `hb` ties it to `r`'s result. -/

/-- `r`'s code with its cleanup (`scrubAll rb d cl`) meets `r`'s contract in
constant time and returns without secret residue. -/
theorem verifiedScrubbedAll {api : Api} (r : Unscrubbed api target) (d : Nat) (cl : Clear) {rb : Nat}
    (hpost : PostOut r.contract rb) (hs : scrubSide r.code d rb cl r.tables = true)
    (hd : d ≤ r.stack := by first | decide | (dsimp only; decide)) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubAll rb d cl r.code) r.contract rb := by
  subst hb
  have h := scrubAll_ok r hs hd hpost
  simp only [scrubSide, Bool.and_eq_true] at hs
  exact ⟨h.1, h.2, retAbi_scrub r hs.2 (wf_of_wfB hs.1.1.2).gs⟩

/-- `verifiedScrubbedAll`, of code that wipes its own frame
(`withStackScratchWiped bytes reg words body`, with no frame inside it): its
cleanup clears the registers `cl` alone, `scrubAll rb 0 cl`, which wipes no
stack. -/
theorem verifiedScrubbedWiped {api : Api} (r : Unscrubbed api target) (bytes : Nat) (reg : Reg)
    (words : Nat) (body : Prog isa) (cl : Clear) {rb : Nat}
    (hc : r.code = withStackScratchWiped bytes reg words body) (hpost : PostOut r.contract rb)
    (hs : wipedSide r.code body bytes words rb cl = true)
    (hst : bytes ≤ r.stack := by first | decide | (dsimp only; decide)) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubAll rb 0 cl r.code) r.contract rb := by
  subst hb
  have h := scrubWiped_ok r hc hs hst hpost
  simp only [wipedSide, Bool.and_eq_true] at hs
  exact ⟨h.1, h.2, retAbi_scrub r hs.2 (wf_of_wfB hs.1.1.2).gs⟩

end VG.PPC64LE.Scrub
