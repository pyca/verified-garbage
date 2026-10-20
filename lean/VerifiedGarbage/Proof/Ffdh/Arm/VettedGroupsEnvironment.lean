module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! Read-only vetted tables remain available throughout a key-generation attempt. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

def RecordSafe (p : BitVec 32) (g : Group) (regions : List Region) : Prop :=
  ∀ r ∈ regions, (⟨State.addr p, 4⟩ : Region).Disjoint r ∧
    (⟨State.addr (p + 4), 4⟩ : Region).Disjoint r ∧
    (⟨State.addr (p + 8), 3 * g.len⟩ : Region).Disjoint r

def TableSafe (p : BitVec 32) : List Group → List Region → Prop
  | [], _ => True
  | g :: gs, regions => RecordSafe p g regions ∧
    TableSafe (p + BitVec.ofNat 32 (8 + 3 * g.len)) gs regions

 theorem RecordAt.after_frame {p : BitVec 32} {g : Group} {s t : State} {rs : List Reg}
    {regions : List Region} (h : RecordAt p g s) (safe : RecordSafe p g regions)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t) : RecordAt p g t := by
  refine ⟨h.positive, h.lenFit, h.bitsFit, h.fit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rest.rd, rest.wr]; exact h.readLen
  · rw [rest.rd, rest.wr]; exact h.readBits
  · rw [frame.readW (r := ⟨State.addr p, 4⟩) (Region.contains_self _ _)
      (fun r hr => (safe r hr).1) (by decide)]; exact h.len
  · rw [frame.readW (r := ⟨State.addr (p + 4), 4⟩) (Region.contains_self _ _)
      (fun r hr => (safe r hr).2.1) (by decide)]; exact h.bits
  · rw [rest.rd, rest.wr]; exact h.read
  · rw [VG.Proof.Rsa.rsa_bytes_frame frame (by have := h.fit; omega)
      (fun r hr => (safe r hr).2.2)]; exact h.bytes

 theorem TableAt.after_frame {p : BitVec 32} {gs : List Group} {s t : State} {rs : List Reg}
    {regions : List Region} (h : TableAt p gs s) (safe : TableSafe p gs regions)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t) : TableAt p gs t := by
  induction gs generalizing p with
  | nil => trivial
  | cons g gs ih => exact ⟨h.1.after_frame safe.1 frame rest, ih h.2 safe.2⟩

/-- A shared table's addresses and contents are independent of the secret scalar. -/
def environment : SampleEnvironment where
  holds p s := TableAt (s.syms tableSym) groups s ∧
    TableSafe (s.syms tableSym) groups (keyCallWrites p s)
  publicRel s t := s.syms tableSym = t.syms tableSym
  stable := by
    intro p s t h frame rest syms
    rw [syms]
    refine ⟨h.1.after_frame h.2 frame rest, ?_⟩
    simpa only [keyCallWrites, keyWrites, rest.sp] using h.2
  public_stable := by
    intro s t u v h left right
    rw [left, right]
    exact h

end VG.Proof.Ffdh.Arm.VettedGroups
