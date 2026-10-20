module
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallLayout

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallGeometry
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! Memory retained across calls to the supplied-nonce signer. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem random_calleeFrame_sub (extra : Nat) (s : State) :
    Region.Sub (below (randomBase s) (extra + 8)) (below (s.gpr .rsp) (extra + 256)) := by
  change Region.Sub ⟨randomBase s - BitVec.ofNat 64 (extra + 8), extra + 8⟩ _
  rw [random_frameBase extra s]
  unfold off
  rw [BitVec.add_sub_cancel]
  exact Region.sub_prefix (by omega)

/-- The callee cannot overwrite any byte of the wrapper's private frame. -/
theorem random_call_frameBytes {extra : Nat} {s : State} {m m' : Mem} (h : RandomSignABI extra s)
    (hf : Frame (randomCallWr s ++ [below (randomBase s) (extra + 8)]) m m') :
    ∀ i < Random.frameBytes, m' (off (randomBase s) i) = m (off (randomBase s) i) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  intro i hi
  apply hf.bytes (R := ⟨randomBase s, Random.frameBytes⟩) _ (by change 248 ≤ 2 ^ 64; decide) hi
  intro r hr
  simp only [randomCallWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.stackOut.sub_left (random_frame_sub h)
  · exact h.stackScratch.sub_left (random_frame_sub h)
  · exact Offset.base_disjoint_below _ (by unfold Random.frameBytes; omega)

/-- Whole-word reads of the retained private frame are unchanged. -/
theorem random_frame_words {B : Addr} {m m' : Mem}
    (h : ∀ i < Random.frameBytes, m' (off B i) = m (off B i)) {d : Nat}
    (hd : d + 8 ≤ Random.frameBytes) : word m' B d = word m B d := by
  apply Mem.readW_congr
  intro i hi
  have he : off B d + BitVec.ofNat 64 i = off B (d + i) := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [he]
  exact h _ (by omega)

/-- An input disjoint from the output, scratch, and reserved stack is retained. -/
theorem random_call_inputBytes {extra : Nat} {s : State} {m m' : Mem} {p : Addr} {n : Nat}
    (hf : Frame (randomCallWr s ++ [below (randomBase s) (extra + 8)]) m m')
    (hout : (⟨p, n⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩)
    (hscratch : (⟨p, n⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩)
    (hstack : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  apply hf.bytes (R := ⟨p, n⟩) _ hn (List.mem_range.mp hi)
  intro r hr
  simp only [randomCallWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hout
  · exact hscratch
  · exact (hstack.sub_left (random_calleeFrame_sub extra s)).symm

/-- Writing the return address leaves every disjoint input byte unchanged. -/
theorem random_callEntry_bytes {s : State} {B p : Addr} {n : Nat} (hsp : s.gpr .rsp = B)
    (hsep : Mem.Sep p n (B - 8) 8) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt s.callEntry.mem p n = Spec.Rsa.bytesAt s.mem p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [State.callEntry_mem, hsp]
  apply Mem.write_apply
  apply hsep
  rw [Mem.sub_ofNat_toNat _ (by omega)]
  exact hi'

/-- Preserve a source through the callee and subsequent private-frame writes. -/
theorem random_call_source {extra : Nat} {s t u : State} {m : Mem} {p : Addr} {bs : List Byte}
    (hsrc : Src t (randomBase s) Random.frameBytes p bs)
    (hf : Frame (randomCallWr s ++ [below (randomBase s) (extra + 8)]) t.mem m)
    (hm : InScr (randomBase s) Random.frameBytes m u.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr)
    (hout : (⟨p, bs.length⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩)
    (hscratch : (⟨p, bs.length⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩)
    (hstack : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, bs.length⟩)
    (hn : bs.length ≤ 2 ^ 64) : Src u (randomBase s) Random.frameBytes p bs := by
  refine ⟨fun i hi => by rw [hrd, hwr]; exact hsrc.rd i hi, ?_, hsrc.out⟩
  intro i hi
  rw [hm _ (hsrc.out i hi)]
  have hbytes := random_call_inputBytes hf hout hscratch hstack hn
  have he := congrArg (fun xs : List Byte => xs[i]?) hbytes
  simp only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range,
    hi, Option.map_some] at he
  exact (Option.some.inj he).trans (hsrc.val i hi)

theorem random_private_bytes {B p : Addr} {n : Nat} {m m' : Mem}
    (hf : InScr B Random.frameBytes m m')
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨B, Random.frameBytes⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  exact hf _ (out_scr hd (contains_byte _ (List.mem_range.mp hi) hn))

end VG.Proof.Dsa.X86_64
