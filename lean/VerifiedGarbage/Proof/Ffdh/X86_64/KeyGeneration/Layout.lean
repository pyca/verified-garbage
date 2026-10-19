module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Data
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Where the key-generation controller's buffers are -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

namespace KeyInput

variable {p : KeyPublic} {s : State}

theorem nowrap (h : KeyInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.1.2.2.2.2.1 r hr

theorem write_disjoint (h : KeyInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.1.2.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : KeyInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r ∧ (below (s.gpr .rsp) stackUse).Disjoint r :=
  h.1.2.2.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : KeyInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.1.2.2.2.2.2.1

theorem len_eq (h : KeyInput p s) : p.len = keyLen s := by rw [← h.2]; rfl

theorem len_bounds (h : KeyInput p s) : 64 ≤ p.len ∧ p.len ≤ 1024 := by
  rw [h.len_eq]; exact h.1.2.2.2.2.2.2.2.2.1

theorem control_scr (h : KeyInput p s) {t : State} (hw : t.wr = s.wr) : Scr t p.control 128 := by
  refine Scr.of_mem (by rw [hw, h.1.2.2.2.1, ← h.2]; simp [inWrites, inCtl, keyOfState]) ?_
  rw [← h.2]
  exact h.nowrap (r := inCtl s) (by simp [inWrites])

/-- The regions the controller (and its callee) may write, and its stack. -/
def changes (s : State) : List Region := inWrites s ++ [below (s.gpr .rsp) stackUse]

theorem changes_of_wr (h : KeyInput p s) {t : State} (hw : t.wr = s.wr) :
    t.wr ++ [below (s.gpr .rsp) stackUse] = changes s := by
  rw [hw, h.1.2.2.2.1]; rfl

theorem read_disjoint (h : KeyInput p s) {r : Region} (hr : r ∈ inReads s) :
    ∀ w ∈ changes s, r.Disjoint w := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (h.write_disjoint hw hr).symm
  · obtain rfl := List.mem_singleton.mp hw
    exact (h.stack_disjoint (List.mem_append_right _ hr)).2.symm

theorem bytes_frame (h : KeyInput p s) {r : Region} (hr : r ∈ inReads s) {m m' : Mem}
    (hf : Frame (changes s) m m') : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hn := h.nowrap (List.mem_append_right _ hr)
  exact hf.bytes (h.read_disjoint hr) (by omega_using [hn]) (List.mem_range.mp hi)

theorem random_frame (h : KeyInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.rp p.randLen = Spec.Rsa.bytesAt m p.rp p.randLen := by
  rw [← h.2]
  exact h.bytes_frame (r := inRand s) (by simp [inReads]) hf

theorem domain_frame (h : KeyInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.dp p.dlen = Spec.Rsa.bytesAt m p.dp p.dlen := by
  rw [← h.2]
  exact h.bytes_frame (r := inDom s) (by simp [inReads]) hf

/-- The writes but the controller's words. -/
def callChanges (s : State) : List Region :=
  [inX s, inY s, inUsed s, inScr s, below (s.gpr .rsp) stackUse]

theorem callChanges_sub (s : State) : ∀ r ∈ callChanges s, ∃ q ∈ changes s, Region.Sub r q := by
  intro r hr
  refine ⟨r, ?_, fun _ hi => hi⟩
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [changes, inWrites]

theorem control_frame (h : KeyInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m')
    (j : Nat) (hj : j < 16) : word m' p.control (8 * j) = word m p.control (8 * j) := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  rw [← h.2]
  refine hf.readW (r := inCtl s) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
    (fun r hr => ?_) (by decide)
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hpw.1.2.2.2.symm
  · exact hpw.2.1.2.2.symm
  · exact hpw.2.2.1.2.symm
  · exact hpw.2.2.2.1.symm
  · exact (h.stack_disjoint (r := inCtl s) (by simp [inWrites])).2.symm

end KeyInput

end VG.Proof.Ffdh.X86_64.KeyGeneration
