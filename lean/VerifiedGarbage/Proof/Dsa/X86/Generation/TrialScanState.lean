module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialDigit
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialAdvance
public import VerifiedGarbage.Proof.Dsa.Generation.Trial
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Proof.Mont.Words32

/-! The trial scan retains its input and tracks its low-word residue. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

def trialClob : List Reg := [.eax, .ecx, .edx, .edi, .ebp]

structure TrialScanInv (s : State) (base : Addr) (offset j : Nat) (t : State) : Prop where
  mem : t.mem = s.mem
  keeps : Keeps trialClob s t
  ptr : t.gpr .ebp = s.gpr .ebp + BitVec.ofNat 32 (4 * j)
  bound : (t.gpr .edi).toNat < 2 * (s.gpr .ebx).toNat
  residue : (t.gpr .edi).toNat * 2 ^ (32 * j) % (s.gpr .ebx).toNat =
    val32 s.mem base offset j % (s.gpr .ebx).toNat

theorem trial_read_keeps {s t : State} {m : MemOp} {rs : List Reg}
    (mem : t.mem = s.mem) (K : Keeps rs s t) (base : m.base ∉ rs) :
    readSrc t (.mem m) = readSrc s (.mem m) := by
  show t.load32 (t.ea m) = s.load32 (s.ea m)
  have addr : t.ea m = s.ea m := by simp only [State.ea, K.1 _ base]
  simp only [State.load32, addr, mem, K.2.1, K.2.2]

theorem trial_scan_step {s u : State} {base : Addr} {size offset n j endSlot : Nat}
    (ws : Rt.Ws s base size) (hp : Rt.PtrAt s base .ebp offset)
    (fit : offset + 4 * n ≤ size) (small : 4 * n < 2 ^ 32) (hj : j < n)
    (prime : 3 ≤ (s.gpr .ebx).toNat ∧ (s.gpr .ebx).toNat < 8162)
    (inverse : ((s.gpr .ebx).toNat * (s.gpr .esi).toNat + 1) % 2 ^ 16 = 0)
    (last : readSrc s (.mem (at_ .esp endSlot)) =
      some (s.gpr .ebp + BitVec.ofNat 32 (4 * n)))
    (h : TrialScanInv s base offset j u) :
    WP isa (.seq (trialCandidateWord 0) (.block (trialAdvance endSlot))) u fun t =>
      TrialScanInv s base offset (j + 1) t ∧ t.zf = some (decide (j + 1 = n)) := by
  have hu : Rt.PtrAt u base .ebp (offset + 4 * j) := by
    rw [Rt.PtrAt, h.ptr]
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 4 * j < 2 ^ 32 by omega)] using
      Rt.ptr_add hp (BitVec.ofNat 32 (4 * j))
  have read := Rt.readSrc_ptr (ws.of_keeps h.keeps) (d := 0) hu (by omega)
  simp only [Nat.add_zero, h.mem] at read
  have up : 3 ≤ (u.gpr .ebx).toNat ∧ (u.gpr .ebx).toNat < 8162 := by
    rw [h.keeps.1 .ebx (by decide)]; exact prime
  have ui : ((u.gpr .ebx).toNat * (u.gpr .esi).toNat + 1) % 2 ^ 16 = 0 := by
    rw [h.keeps.1 .ebx (by decide), h.keeps.1 .esi (by decide)]; exact inverse
  have ua : (u.gpr .edi).toNat < 2 * (u.gpr .ebx).toNat := by
    rw [h.keeps.1 .ebx (by decide)]; exact h.bound
  refine WP.seq (WP.mono (trial_candidate_word read ua up ui) ?_)
  rintro v ⟨bound, residue, mem, K⟩
  have memv : v.mem = s.mem := mem.trans h.mem
  have Kv : Keeps trialClob s v := h.keeps.trans (K.mono (by decide))
  have lastv := (trial_read_keeps memv Kv (m := at_ .esp endSlot) (by change .esp ∉ trialClob; decide)).trans last
  refine WP.mono (trial_advance lastv) ?_
  rintro t ⟨ptr, zf, mem', K'⟩
  have Kt : Keeps trialClob s t := Kv.trans (K'.mono (by decide))
  have vp : v.gpr .ebp = s.gpr .ebp + BitVec.ofNat 32 (4 * j) := by
    rw [K.1 .ebp (by decide), h.ptr]
  refine ⟨⟨mem'.trans memv, Kt, ?_, ?_, ?_⟩, ?_⟩
  · rw [ptr, vp, row_ebp]
  · rw [K'.1 .edi (by decide)]
    rw [h.keeps.1 .ebx (by decide)] at bound
    exact bound
  · rw [h.keeps.1 .ebx (by decide)] at residue
    have result := VG.Proof.Dsa.Generation.trial_word_step residue h.residue
    rw [val32_succ, K'.1 .edi (by decide)]
    exact result
  · rw [zf, vp, row_zf _ hj small]

end VG.Proof.Dsa.X86.Generation
