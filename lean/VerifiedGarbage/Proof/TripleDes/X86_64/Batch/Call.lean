module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Frame
public import VerifiedGarbage.Proof.TripleDes.X86_64.EcbCall.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.TripleDes.Cbc
public import VerifiedGarbage.Proof.TripleDes.X86_64.SpSafe
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Modes.X86_64.Steps
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Lit

/-!
# Triple DES on x86-64: the ECB functions, as the modes call them

An `EcbImpl` is an implementation of `vg_triple_des_ecb_encrypt` and
`vg_triple_des_ecb_decrypt` (the baseline one, or a variant: `sse`, `avx2`,
`avx512`), as registered (`Artifacts/TripleDes/X86_64.lean`): its code with its
working space in a frame of its own, proven against the shared contract with
1040 bytes of stack. It is a variant of the interface `TripleDesEcb` on x86-64
(`Variants/TripleDesEcb/X86_64/`), over which the batched modes are generic
(`Generic/TripleDesEcb/X86_64/`).

`ecb_call`: a call of one of its functions on `n` blocks at `D` in place,
under the schedule at `K`, from the contract (with `WP.callF`): each block
then holds the cipher's (`blockCipher`, `CIPH_K` or `CIPH⁻¹_K` on 8 bytes) of
what it held, and only the blocks and the stack below the stack pointer
change. `ecb_rel`: such calls, with the same arguments in both runs, are
constant time.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Batch

open VG VG.X86_64
open VG.Spec.TripleDes (Direction)

/-- An implementation of the ECB functions, in both directions. -/
structure EcbImpl where
  /-- What the names of the functions and of their callers' instances end
  with (e.g. `_avx2`; nothing for the baseline). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The function of each direction, in its frame. -/
  code : Direction → Prog isa
  verified : ∀ d, Verified X86_64.target (code d) (Spec.TripleDes.ecbContract X86_64.abi d 1040)
  spSafe : ∀ d, SpSafe (code d)
  depth : ∀ d, (code d).x86_64Depth ≤ 1040
  noMxcsr : ∀ d, (code d).allInstrs (fun i => !loadsMxcsr i) = true

/-- The name of the function of the direction `d`. -/
def EcbImpl.name (v : EcbImpl) : Direction → String
  | .encrypt => "vg_triple_des_ecb_encrypt" ++ v.suffix
  | .decrypt => "vg_triple_des_ecb_decrypt" ++ v.suffix

/-- The registered code around the ECB code `c` of either direction. -/
abbrev framed (c : Prog isa) : Prog isa := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128 c

theorem framed_depth {c : Prog isa} (h : c.x86_64Depth ≤ 8) : (framed c).x86_64Depth ≤ 1040 := by
  simp only [framed, Impl.StackScratch.X86_64.withStackScratchWiped, Impl.StackScratch.X86_64.withStackScratch,
    Code.x86_64Depth, Instr.frameBytes, Nat.zero_max, Nat.max_zero]
  exact Nat.add_le_add_right h 1032


/-! ## No ECB code loads MXCSR -/

section
open Impl.TripleDes.X86_64

theorem bitslice_mx (d : Direction) : (Bitslice.ecb d).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases d
  · show Bitslice.encrypt.allInstrs _ = true; lit_decide
  · show Bitslice.decrypt.allInstrs _ = true; lit_decide

theorem sse_mx (d : Direction) : (BitsliceSse.ecb d).allInstrs (fun i => !loadsMxcsr i) = true := by
  show ((BitsliceSse.wide d).allInstrs _ && (Bitslice.ecb d).allInstrs _) = true
  rw [bitslice_mx, Bool.and_true]
  cases d <;> lit_decide

theorem avx2_mx (d : Direction) : (BitsliceAvx2.ecb d).allInstrs (fun i => !loadsMxcsr i) = true := by
  show ((BitsliceAvx2.wide d).allInstrs _ && (BitsliceSse.ecb d).allInstrs _) = true
  rw [sse_mx, Bool.and_true]
  cases d <;> lit_decide

theorem avx512_mx (d : Direction) : (BitsliceAvx512.ecb d).allInstrs (fun i => !loadsMxcsr i) = true := by
  show ((BitsliceAvx512.wide d).allInstrs _ && (BitsliceAvx2.ecb d).allInstrs _) = true
  rw [avx2_mx, Bool.and_true]
  cases d <;> lit_decide

theorem framed_mx {c : Prog isa} (h : c.allInstrs (fun i => !loadsMxcsr i) = true) :
    (framed c).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [framed, Impl.StackScratch.X86_64.withStackScratchWiped, Impl.StackScratch.X86_64.withStackScratch,
    Code.allInstrs, h, Bool.and_true, Bool.true_and]
  decide

end

/-- The baseline implementation, `vg_triple_des_ecb_encrypt` and `_decrypt`. -/
def sse : EcbImpl where
  suffix := ""
  features := []
  code d := framed (Impl.TripleDes.X86_64.EcbCall.sse d)
  verified d := ecb_framed (EcbCall.sse_verified d) (Code.all_of_allInstrs (EcbCall.sse_sp d)) (EcbCall.sse_depth d)
  spSafe d := SpSafe.of_all (ecb_spSafe (EcbCall.sse_sp d))
  depth d := framed_depth (EcbCall.sse_depth d)
  noMxcsr d := framed_mx (by cases d <;> exact sse_mx _)

/-- The AVX2 implementation, `vg_triple_des_ecb_encrypt_avx2` and `_decrypt_avx2`. -/
def avx2 : EcbImpl where
  suffix := "_avx2"
  features := ["avx", "avx2"]
  code d := framed (Impl.TripleDes.X86_64.EcbCall.avx2 d)
  verified d := ecb_framed (EcbCall.avx2_verified d) (Code.all_of_allInstrs (EcbCall.avx2_sp d))
    (EcbCall.avx2_depth d)
  spSafe d := SpSafe.of_all (ecb_spSafe (EcbCall.avx2_sp d))
  depth d := framed_depth (EcbCall.avx2_depth d)
  noMxcsr d := framed_mx (by cases d <;> exact avx2_mx _)

/-- The AVX-512 implementation, `vg_triple_des_ecb_encrypt_avx512` and `_decrypt_avx512`. -/
def avx512 : EcbImpl where
  suffix := "_avx512"
  features := ["avx", "avx2", "avx512f"]
  code d := framed (Impl.TripleDes.X86_64.EcbCall.avx512 d)
  verified d := ecb_framed (EcbCall.avx512_verified d) (Code.all_of_allInstrs (EcbCall.avx512_sp d))
    (EcbCall.avx512_depth d)
  spSafe d := SpSafe.of_all (ecb_spSafe (EcbCall.avx512_sp d))
  depth d := framed_depth (EcbCall.avx512_depth d)
  noMxcsr d := framed_mx (by cases d <;> exact avx512_mx _)

/-- The stack below the stack pointer that a call uses: its return address
and the callee's 1040 bytes. -/
abbrev stkN : Nat := 1048

/-- The cipher of the direction `d` on blocks as lists of 8 bytes: `CIPH_K` or
`CIPH⁻¹_K`. -/
def blockCipher (k : Spec.TripleDes.Schedule) : Direction → Spec.Cbc.Cipher
  | .encrypt => Spec.TripleDes.cipher k
  | .decrypt => Spec.TripleDes.invCipher k

theorem blockCipher_length (k : Spec.TripleDes.Schedule) (d : Direction) (b : List Byte) :
    (blockCipher k d b).length = 8 := by
  cases d <;> simp [blockCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher]

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The return address and the reserved stack of the callee's contract,
from the state after the call stored its return address: within `stkN`
bytes below the caller's stack pointer. -/
theorem reserved_stk (sp : Addr) :
    Region.Sub ⟨sp - 8, 8⟩ (below sp stkN) ∧ Region.Sub ⟨sp - 8 - BitVec.ofNat 64 1040, 1040⟩ (below sp stkN) := by
  refine ⟨Offset.sub_below sp (a := 8) (by decide) (by decide), ?_⟩
  rw [show sp - 8 - BitVec.ofNat 64 1040 = sp - BitVec.ofNat 64 1048 by
    rw [BitVec.sub_sub]; rfl]
  exact Offset.sub_below sp (by decide) (by decide)

theorem below8_stk (sp : Addr) : Region.Sub (below sp 8) (below sp stkN) :=
  Offset.sub_below sp (by decide) (by decide)

/-- What a call of an ECB function needs: the schedule at `K` and `n` blocks
at `D`, apart from each other and from the stack the call uses. -/
structure EcbCallPre (s : State) (K D : Addr) (n : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = D
  rdx : s.gpr .rdx = BitVec.ofNat 64 n
  sp : stkN ≤ (s.gpr .rsp).toNat
  kw : K.toNat + 384 ≤ 2 ^ 64
  wrap : D.toNat + 8 * n ≤ 2 ^ 64
  kd : (⟨K, 384⟩ : Region).Disjoint ⟨D, 8 * n⟩
  stkK : (below (s.gpr .rsp) stkN).Disjoint ⟨K, 384⟩
  stkD : (below (s.gpr .rsp) stkN).Disjoint ⟨D, 8 * n⟩
  reads : Covers ([⟨K, 384⟩] ++ [⟨D, 8 * n⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 8 * n⟩] s.wr

/-- What a call of the ECB function of the direction `d` leaves. -/
structure EcbCallPost (d : Direction) (s : State) (K D : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨D, 8 * n⟩, below (s.gpr .rsp) stkN] s.mem s'.mem
  out : ∀ j < n, ∀ u < 8, s'.mem (D + BitVec.ofNat 64 (8 * j + u)) =
    (blockCipher (Spec.TripleDes.scheduleAt s.mem K) d
      (Spec.TripleDes.bytesAt s.mem (D + BitVec.ofNat 64 (8 * j)) 8)).getD u 0

theorem EcbCallPre.pre {d : Direction} {s : State} {K D : Addr} {n : Nat} (h : EcbCallPre s K D n) :
    (Spec.TripleDes.ecbContract X86_64.abi d 1040).pre
      (s.callEntry.withRegions [⟨K, 384⟩] [⟨D, 8 * n⟩]) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  have ⟨rR, rS⟩ := reserved_stk (s.gpr .rsp)
  sig_pre [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, X86_64.abi, X86_64.argRegs]
  simp only [h.rdi, h.rsi, h.rdx, hn, Nat.mul_comm n 8]
  have hsp := h.sp
  have hN : stkN = 1048 := rfl
  refine ⟨?_, trivial, trivial, h.kd, (h.stkK.sub_left rR), (h.stkD.sub_left rR),
    (h.stkK.sub_left rS), (h.stkD.sub_left rS), h.kw, h.wrap⟩
  rw [BitVec.toNat_sub, show (8 : Addr).toNat = 8 from rfl]; omega

/-- The ECB postcondition, byte by byte. -/
theorem ecb_bytes {d : Direction} {k : Spec.TripleDes.Schedule} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.TripleDes.blocksAt m' D n = Spec.TripleDes.ecb k d (Spec.TripleDes.blocksAt m D n)) :
    ∀ j < n, ∀ u < 8, m' (D + BitVec.ofNat 64 (8 * j + u)) =
      (blockCipher k d (Spec.TripleDes.bytesAt m (D + BitVec.ofNat 64 (8 * j)) 8)).getD u 0 := by
  intro j hj u hu
  have hb := congrArg (fun l => l[j]?) h
  simp only [Spec.TripleDes.blocksAt, Spec.TripleDes.ecb, List.map_map, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.some.injEq] at hb
  have hv := congrArg (fun b : Spec.TripleDes.Block => b[u]'hu) hb
  have hofn : (Vector.ofFn fun i : Fin 8 => (Spec.TripleDes.bytesAt m (D + BitVec.ofNat 64 (8 * j)) 8).getD i.val 0) =
      Spec.TripleDes.blockAt m (D + BitVec.ofNat 64 (8 * j)) := by
    apply Vector.ext
    intro i hi
    simp [Spec.TripleDes.bytesAt, Spec.TripleDes.blockAt, List.getD_eq_getElem?_getD]
  have ha : D + BitVec.ofNat 64 (8 * j + u) = D + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 u := by
    rw [Modes.X86_64.addr_add]
  cases d <;>
  · simp only [Function.comp_apply, Spec.TripleDes.blockAt, Vector.getElem_ofFn] at hv
    rw [ha, hv]
    simp only [blockCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, hofn]
    rw [List.getD_eq_getElem?_getD, Vector.getElem?_toList]
    simp [hu, Spec.TripleDes.blockAt]

/-- The schedule depends only on its 384 bytes. -/
theorem scheduleAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 384, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    Spec.TripleDes.scheduleAt m' p = Spec.TripleDes.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.TripleDes.scheduleAt, Vector.getElem_ofFn]
  have : ∀ (l : List Nat), (∀ j ∈ l, j < 8) → ∀ init : BitVec 64,
      l.foldl (fun out j => out ||| (m' (p + BitVec.ofNat 64 (8 * i + j))).zeroExtend 64 <<< (8 * j)) init =
      l.foldl (fun out j => out ||| (m (p + BitVec.ofNat 64 (8 * i + j))).zeroExtend 64 <<< (8 * j)) init := by
    intro l hl
    induction l with
    | nil => intro _; rfl
    | cons j l ih =>
      intro init
      simp only [List.foldl_cons]
      rw [h _ (by have := hl j List.mem_cons_self; omega)]
      exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _
  exact this _ (fun j hj => List.mem_range.mp hj) 0

theorem ecb_call (v : EcbImpl) (d : Direction) {s : State} {K D : Addr} {n : Nat} (h : EcbCallPre s K D n) :
    WP isa (.call (v.name d) (v.code d)) s (EcbCallPost d s K D n) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  refine WP.callF (k := Spec.TripleDes.ecbContract X86_64.abi d 1040) (v.verified d).1 (v.spSafe d)
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right (v.depth d) 16) (by decide))
    (rd := [⟨K, 384⟩]) (wr := [⟨D, 8 * n⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf ⟨s₂, hm₂, _, hpost⟩ _
  sig_post [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, X86_64.abi,
    X86_64.argRegs] at hpost
  rw [h.rdi, h.rsi, h.rdx, hn, hm₂] at hpost
  have fE := callEntry_frame s
  rw [State.callEntry_mem] at fE
  have s8 := below8_stk (s.gpr .rsp)
  have hN : stkN = 1048 := rfl
  have eK := scheduleAt_congr (m := s.mem) (m' := s.mem.writeW (s.gpr .rsp - 8) (s.unknowns 0)) (p := K)
    fun i hi => fE.bytes (R := ⟨K, 384⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.stkK.sub_left s8).symm) (by show 384 ≤ 2 ^ 64; decide) hi
  have out := ecb_bytes hpost
  refine ⟨hrd, hwr, hcs, hf.sub fun r hr => ?_, fun j hj u hu => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨below (s.gpr .rsp) stkN, by simp, Offset.sub_below _ (by have := v.depth d; omega)
        (by have := v.depth d; omega)⟩
  · rw [out j hj u hu, eK]
    rw [Proof.TripleDes.bytesAt_eq_of_frame _ 8 fE (by decide) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.stkD.sub_right (Offset.sub_base D (by omega))).sub_left s8).symm)]

/-- Calls of an ECB function, with the same arguments in both runs, are
constant time. -/
theorem ecb_rel (v : EcbImpl) (d : Direction) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K D : Addr, ∃ n : Nat,
      EcbCallPre s₁ K D n ∧ EcbCallPre s₂ K D n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call (v.name d) (v.code d)) fun _ _ => True := by
  refine RelCT.callEx (v.verified d).1 (v.verified d).2.1 fun s₁ s₂ hp => ?_
  obtain ⟨K, D, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  sig_pub [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, X86_64.abi, X86_64.argRegs]
  simp only [h₁.rdi, h₁.rsi, h₁.rdx, h₂.rdi, h₂.rsi, h₂.rdx, hsp]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.TripleDes.X86_64.Batch
