module

public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFrame
import Mathlib.Data.Nat.Basic

/-! ### `Dsa.X86_64.RandomSignCallGeometry`, which this module and modules that import it used -/

section

/-! Relative positions of the wrapper, callee stack, nonce, and call arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomStackBase (extra : Nat) (s : State) : Addr :=
  s.gpr .rsp - BitVec.ofNat 64 (extra + 256)

theorem random_callBase (extra : Nat) (s : State) :
    randomBase s - 8 = off (randomStackBase extra s) extra := by
  unfold randomBase Random.frameBytes randomStackBase off
  rw [BitVec.sub_sub, show BitVec.ofNat 64 248 + 8 = BitVec.ofNat 64 256 from rfl,
    Nat.add_comm extra 256, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem random_frameBase (extra : Nat) (s : State) :
    randomBase s = off (randomStackBase extra s) (extra + 8) := by
  have hc := random_callBase extra s
  have he := congrArg (fun x : Addr => x + 8) hc
  rw [BitVec.sub_add_cancel] at he
  rw [he]
  simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem random_nonceBase (extra : Nat) (s : State) :
    off (randomBase s) Random.oNonce = off (randomStackBase extra s) (extra + 208) := by
  rw [random_frameBase extra s]
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
  rfl

theorem random_calleeBase (extra : Nat) (s : State) :
    randomBase s - 8 - BitVec.ofNat 64 extra = randomStackBase extra s := by
  rw [random_callBase extra s]
  exact BitVec.add_sub_cancel _ _

theorem randomStackBase_toNat {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    (randomStackBase extra s).toNat = (s.gpr .rsp).toNat - (extra + 256) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  simp only [randomStackBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using [hl]

theorem randomStack_offset_toNat {extra : Nat} {s : State} (h : RandomSignABI extra s)
    {d : Nat} (hd : d ≤ extra + 256) :
    (off (randomStackBase extra s) d).toNat = (randomStackBase extra s).toNat + d := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hk := randomStackBase_toNat h
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hd, hl, hk]

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RandomSignCallLayout`, which this module and modules that import it used -/

section

/-! Memory layout of the supplied-nonce call within the randomized wrapper. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomCallRd (s : State) : List Region :=
  [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
    ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨randomBase s, 40⟩]

def randomCallWr (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩]

def randomCallArg (s : State) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => stackArg s 0
  | 1 => stackArg s 1
  | 2 => stackArg s 2
  | 3 => stackArg s 5
  | _ => stackArg s 6

theorem random_call_stackArg {t : State} {B : Addr} (hsp : t.gpr .rsp = B)
    (rd wr : List Region) {i : Nat} (hi : i < 5) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem B (8 * i) := by
  have he : B - 8 + BitVec.ofNat 64 (8 * (i + 1)) = off B (8 * i) := by
    rw [show 8 * (i + 1) = 8 + 8 * i by omega_using [], BitVec.ofNat_add,
      ← BitVec.add_assoc, show BitVec.ofNat 64 8 = (8 : BitVec 64) from rfl, BitVec.sub_add_cancel]
  have hsep : Mem.Sep (B - 8 + BitVec.ofNat 64 (8 * (i + 1))) 8 (B - 8) 8 :=
    fun x hx hy => Offset.sep_base (B - 8) (by omega_using []) (by omega_using [hi]) x hy hx
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_rsp, State.callEntry_mem, hsp]
  rw [Mem.readW_writeW_sep hsep (by decide), he]

theorem random_call_stackArgAddr {t : State} {B : Addr} (hsp : t.gpr .rsp = B)
    (rd wr : List Region) : stackArgAddr (t.callEntry.withRegions rd wr) 0 = B := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp]
  exact BitVec.sub_add_cancel _ _

/-- The call's read and write permissions are covered by the wrapper's permissions. -/
theorem random_call_covers {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (randomCallRd s ++ randomCallWr s) (t.rd ++ t.wr) ∧ Covers (randomCallWr s) t.wr := by
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  have hf : (⟨randomBase s, Random.frameBytes⟩ : Region) ∈ t.wr := by rw [hwr]; exact .head _
  have ho : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have hs : (⟨stackArg s 5, (stackArg s 6).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have zero (p : Addr) : p = p + BitVec.ofNat 64 0 := (BitVec.add_zero p).symm
  have cw : Covers (randomCallWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [randomCallWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, ho, 0, zero _, by simp⟩
    · exact ⟨_, hs, 0, zero _, by simp⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  simp only [randomCallRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_append_left _ (by rw [hrd, h.rd]; simp), 0, zero _, by simp⟩
  · exact ⟨_, List.mem_append_right _ hf, 200, rfl, by change 200 + (stackArg s 0).toNat ≤ 248; omega_using [hq]⟩
  · exact ⟨_, List.mem_append_left _ (by rw [hrd, h.rd]; simp), 0, zero _, by simp⟩
  · exact ⟨_, List.mem_append_right _ hf, 0, zero _, by change 0 + 40 ≤ 248; decide⟩

end VG.Proof.Dsa.X86_64

end

end

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
  exact Region.sub_prefix (by omega_using [])

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
  · exact Offset.base_disjoint_below _ (by unfold Random.frameBytes; omega_using [hl])

/-- Whole-word reads of the retained private frame are unchanged. -/
theorem random_frame_words {B : Addr} {m m' : Mem}
    (h : ∀ i < Random.frameBytes, m' (off B i) = m (off B i)) {d : Nat}
    (hd : d + 8 ≤ Random.frameBytes) : word m' B d = word m B d := by
  apply Mem.readW_congr
  intro i hi
  have he : off B d + BitVec.ofNat 64 i = off B (d + i) := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [he]
  exact h _ (by omega_using [hd, hi])

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
  rw [Mem.sub_ofNat_toNat _ (by omega_using [hn, hi'])]
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
