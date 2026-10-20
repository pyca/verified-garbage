module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
import VerifiedGarbage.Proof.Dsa.X86.Generation.Dispatch

/-! # All supported widths share one verified search implementation -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem GenerationResult.prepend {P : SearchContextPlan} {s a t : State} {rs : List Reg}
    (result : GenerationResult P a t) (mem : a.mem = s.mem) (K : Keeps rs s a) (sp : .esp ∉ rs) :
    GenerationResult P s t := by
  obtain ⟨ax, bytes, O, rd, wr, esp⟩ := result
  exact ⟨ax, bytes, by rw [← mem]; exact O, rd.trans K.2.1, wr.trans K.2.2, esp.trans (K.1 _ sp)⟩

theorem dispatchGenerate_ok (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn)
    {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State}
    (R : SearchStorage P W s) (cursor : W 16 = 0)
    (seeds : P.seeds.bytes.length % P.geometry.qLen = 0)
    (hs : P.hs.bytes.length % P.geometry.pLen = 0)
    (length : P.saved 7 = BitVec.ofNat 32 (2 * P.geometry.pLen + P.geometry.qLen))
    (room : (P.saved 6).toNat + (2 * P.geometry.pLen + P.geometry.qLen) ≤ 2 ^ 32)
    (apart : (P.geometry.part packed (2 * P.geometry.pLen + P.geometry.qLen)).Disjoint
      ⟨(P.saved 6).setWidth 64, 2 * P.geometry.pLen + P.geometry.qLen⟩)
    (write : ∀ i, i < 2 * P.geometry.pLen + P.geometry.qLen → InRegions s.wr (off ((P.saved 6).setWidth 64) i) 1) :
    WP isa (dispatch H.sha1 H.sha256 F.name F.code) s (GenerationResult P s) := by
  have len := (R.fixed 17 (by decide) (by decide)).trans P.pLength
  have sizes := P.geometry.lengths
  have run {H' : Hash} (Khash : HashOK H') {a : State} (mem : a.mem = s.mem) (K : Keeps [.eax] s a)
      (digest : H'.D = P.geometry.qLen) (final : H'.F = P.geometry.qLen)
      (hash : ∀ bs, Khash.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.geometry.qLen) bs)
      (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * P.geometry.qLen) bs).length = P.geometry.qLen) :
      WP isa (generate H' F.name F.code P.geometry.pLen P.geometry.qLen) a (GenerationResult P s) := by
    have Ra := R.keep (by rw [mem]; exact Frame.refl _ _) K (by decide)
    exact WP.mono (generate_ok Khash F Ra cursor digest final hash hashSize seeds hs length room apart
      (by intro i hi; rw [K.2.2]; exact write i hi)) fun _ result => result.prepend mem K (by decide)
  apply dispatch_ok R.arena.frame R.representation
  · intro a mem K h
    have p : P.geometry.pLen = 128 := by
      rw [len] at h
      have ht := congrArg BitVec.toNat h
      have pw := P.geometry.width
      change P.geometry.pLen % 2 ^ 32 = 128 at ht
      omega
    have q : P.geometry.qLen = 20 := by rcases sizes with h | h | h <;> omega
    rw [← p, ← q]
    apply run H.h1 mem K
    · rw [q]; exact H.width1
    · rw [q]; exact H.final1
    · rw [q]; exact H.hash1
    · rw [q]; exact H.size1
  · intro a mem K h
    have p : P.geometry.pLen = 256 := by
      rw [len] at h
      have ht := congrArg BitVec.toNat h
      have pw := P.geometry.width
      change P.geometry.pLen % 2 ^ 32 = 256 at ht
      omega
    have q : P.geometry.qLen = 32 := by rcases sizes with h | h | h <;> omega
    rw [← p, ← q]
    apply run H.h256 mem K
    · rw [q]; exact H.width256
    · rw [q]; exact H.final256
    · rw [q]; exact H.hash256
    · rw [q]; exact H.size256
  · intro a mem K h1 h2
    have p : P.geometry.pLen = 384 := by
      have pw := P.geometry.width
      rcases pw with p | p | p
      · exact False.elim (h1 (by rw [len, p]; rfl))
      · exact False.elim (h2 (by rw [len, p]; rfl))
      · exact p
    have q : P.geometry.qLen = 32 := by rcases sizes with h | h | h <;> omega
    rw [← p, ← q]
    apply run H.h256 mem K
    · rw [q]; exact H.width256
    · rw [q]; exact H.final256
    · rw [q]; exact H.hash256
    · rw [q]; exact H.size256
end VG.Proof.Dsa.X86.Generation
