module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP on x86-64: the pieces that keep `rsp`, MXCSR and the stack

Each piece but the RSA operation's call is `Good` (`Stack.lean`): its
instructions, and those of the streaming hash functions it calls, never
write `rsp` or load MXCSR, and its calls nest at most two deep.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (seqs round mgfXor xorOut ldSel initD updD finD)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)

/-- What the pieces need of a hash function's streaming functions. -/
structure HGood (H : Stream) : Prop where
  init : H.initC.allInstrs okI = true
  upd : H.updC.allInstrs okI = true
  fin : H.finC.allInstrs okI = true
  initD : H.initC.depth ≤ 1
  updD : H.updC.depth ≤ 1
  finD : H.finC.depth ≤ 1

theorem HGood.of {H : Hash} (hH : HashOK H) (K : Callees H) : HGood H.stream :=
  ⟨okI_all_of hH.initSp K.iMx, okI_all_of hH.updSp hH.updMx, okI_all_of hH.finSp hH.finMx, hH.initDepth,
    hH.updDepth, hH.finDepth⟩

variable {hs : List (Nat × Stream)} (g : ∀ p ∈ hs, HGood p.2)
include g

/-- A call, of the hash function the selector names, of one of its
streaming functions (`f`, with `hf` its facts), from the slot `sl`. -/
theorem callD_good {f : Stream → Prog isa} (hf : ∀ H, HGood H → (f H).allInstrs okI = true ∧ (f H).depth ≤ 2)
    (sl : Nat) :
    Good (.seq (.block (ldSel sl)) (Impl.Dispatch.X86_64.chain (hs.map fun p => (p.1, f p.2)))) := by
  have hc : ∀ c ∈ hs.map (fun p => (p.1, f p.2)), c.2.allInstrs okI = true ∧ c.2.depth ≤ 2 := fun c hc => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact hf p.2 (g p hp)
  refine ⟨?_, ?_⟩
  · have := Proof.Dispatch.chain_allInstrs (test := Impl.Dispatch.X86_64.test) (eq := Cond.e) okI (fun _ => rfl) _
      fun c h => (hc c h).1
    show ((Code.block (ldSel sl) : Prog isa).allInstrs okI &&
      (Impl.Dispatch.chain (M := isa) Impl.Dispatch.X86_64.test Cond.e
        (hs.map fun p => (p.1, f p.2))).allInstrs okI) = true
    rw [this]; rfl
  · show max 0 _ ≤ 2
    have := Proof.Dispatch.X86_64.chain_depth _ fun c h => (hc c h).2
    omega

theorem initD_good (sl : Nat) : Good (initD hs sl) :=
  callD_good g (f := fun H => .call H.initN H.initC) (fun _ h => ⟨h.init, by simp only [Code.depth]; have := h.initD; omega⟩) sl

theorem updD_good (sl : Nat) : Good (updD hs sl) :=
  callD_good g (f := fun H => .call H.updN H.updC) (fun _ h => ⟨h.upd, by simp only [Code.depth]; have := h.updD; omega⟩) sl

theorem finD_good (sl : Nat) : Good (finD hs sl) :=
  callD_good g (f := fun H => .call H.finN H.finC) (fun _ h => ⟨h.fin, by simp only [Code.depth]; have := h.finD; omega⟩) sl

omit g in
theorem Good.seq {a b : Prog isa} (ha : Good a) (hb : Good b) : Good (.seq a b) :=
  ⟨by simp only [Code.allInstrs, ha.1, hb.1, Bool.and_self], by simp only [Code.depth, Nat.max_le]; exact ⟨ha.2, hb.2⟩⟩

omit g in
theorem Good.block' {is : List Instr} (h : (Code.block is : Prog isa).allInstrs okI = true) : Good (.block is) :=
  ⟨h, by simp [Code.depth]⟩

theorem hashLabel_good (o : Nat) : Good (hashLabel hs o) := by
  unfold hashLabel seqs seqs seqs seqs seqs
  exact .seq (.block' rfl) (.seq (initD_good g _) (.seq (.block' rfl) (.seq (updD_good g _) (.seq (.block' rfl)
    (finD_good g _)))))

theorem mgfXor_good : Good (mgfXor lay hs) := by
  have hr : Good (round lay hs) := by
    unfold round seqs seqs seqs seqs seqs seqs seqs seqs seqs
    exact .seq (.block' rfl) (.seq (initD_good g _) (.seq (.block' rfl) (.seq (updD_good g _) (.seq (.block' rfl)
      (.seq (updD_good g _) (.seq (.block' rfl) (.seq (finD_good g _) (.seq ⟨rfl, by
        simp [xorOut, seqs, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩ (.block' rfl)))))))))
  exact .seq (.block' rfl) ⟨hr.1, by simp only [Code.depth]; exact hr.2⟩

omit g in
theorem block_good (is : List Instr) (h : (Code.block is : Prog isa).allInstrs okI = true) : Good (.block is) :=
  ⟨h, by simp [Code.depth]⟩

omit g in
theorem clearEm_good : Good clearEm := ⟨rfl, by simp [clearEm, Code.depth]⟩

omit g in
theorem putMsg_good : Good putMsg := ⟨rfl, by simp [putMsg, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

omit g in
theorem zeroOut_good : Good zeroOut := ⟨rfl, by simp [zeroOut, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

omit g in
theorem copySeed_good : Good copySeed :=
  ⟨rfl, by simp [copySeed, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

omit g in
theorem copyLh_good : Good copyLh :=
  ⟨rfl, by simp [copyLh, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

omit g in
theorem dbArgs_good : Good (.block dbArgs) := ⟨rfl, by simp [Code.depth]⟩

omit g in
theorem seedArgs_good : Good (.block seedArgs) := ⟨rfl, by simp [Code.depth]⟩

omit g in
theorem pubArgs_good : Good (.block pubArgs) := ⟨rfl, by simp [Code.depth]⟩

omit g in
/-- A dispatch to a block for each hash function (`f`). -/
theorem chainB_good {f : Stream → List Instr} (hf : ∀ H, (Code.block (f H) : Prog isa).allInstrs okI = true) :
    Good (Impl.Dispatch.X86_64.chain (hs.map fun p => (p.1, .block (f p.2)))) := by
  have hc : ∀ c ∈ hs.map (fun p => (p.1, (Code.block (f p.2) : Prog isa))),
      c.2.allInstrs okI = true ∧ c.2.depth ≤ 2 := fun c hc => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hc
    exact ⟨hf p.2, by simp [Code.depth]⟩
  exact ⟨Proof.Dispatch.chain_allInstrs (test := Impl.Dispatch.X86_64.test) (eq := Cond.e) okI (fun _ => rfl) _
      fun c h => (hc c h).1, Proof.Dispatch.X86_64.chain_depth _ fun c h => (hc c h).2⟩

omit g in
theorem selPrologue_good (jH jG : Nat) : Good (selPrologue hs jH jG) := by
  unfold selPrologue seqs seqs seqs
  exact .seq (.block' rfl) (.seq (chainB_good (f := fun H => consts H.D) fun _ => rfl) (.seq (.block' rfl)
    (chainB_good (f := fun G => [.mov32 .rax (im G.D), .store (Impl.Mgf1.X86_64.sp sGD) .rax]) fun _ => rfl)))

omit g in
theorem Good.all {c : Prog isa} (h : Good c) : c.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by
    rw [Code.allInstrs_eq]
    exact List.all_eq_true.mpr fun i hi => by rw [SpSafe.of_noSp h.noSp i hi]; rfl)

end VG.Proof.RsaOaep.X86_64
