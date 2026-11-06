module

public import VerifiedGarbage.Proof.Idea.X86_64.FbVerified
public import VerifiedGarbage.Impl.Idea.X86_64.CfbFinal
public import VerifiedGarbage.Proof.Modes.X86_64.CfbFinal
public import VerifiedGarbage.Spec.Idea.CfbFinal
import VerifiedGarbage.Proof.Modes.CfbFinal
import VerifiedGarbage.Proof.Idea.ModeBytes
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Idea.X86_64.ModesLit

/-!
# IDEA-CFB64 of a message's last piece on x86-64 meets its contract

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`: the modes' final function
(`Proof.Modes.X86_64.cfbFinal_wp`) around IDEA's CFB64 functions, whose
contracts (`cfbEncX86_64`, `cfbDecX86_64`) hold where it inlines them
(`call₁_pre`, `call₂_pre`), and whose results it composes into
`Spec.Cfb.EncryptFinal` and `DecryptFinal` (`Proof.Modes.cfbEncFinal_of`, …).
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64
open VG.Proof.Modes.X86_64 (FinalOk Call₁ Call₂ After₁ frameRegion blockAddr slotsRegion frameSp sub_add_ofNat)
open VG.Spec.Aes (bytesAt)

/-- The precondition of the final functions on x86-64: the feedback modes'
with the data `len = rcx` bytes long, and the 80 bytes below `rsp`, which
the frame takes, outside the buffers. -/
def finalPre (s : State) : Prop :=
  fbPre (fun s => (s.gpr .rcx).toNat) s ∧ 80 ≤ (s.gpr .rsp).toNat ∧
    ∀ r ∈ ([⟨s.gpr .rdi, 104⟩, ⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, 8 * 22⟩] : List Region),
      (frameRegion s).Disjoint r

theorem finalArgs_ok : FinalOk finalArgs :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The first function's regions: the schedule, and the IV, the whole blocks
and the scratch buffer. -/
def rdW (s₀ : State) : List Region := [⟨s₀.gpr .rdi, 104⟩]
def wrW (s₀ : State) : List Region :=
  [⟨s₀.gpr .rsi, 8⟩, ⟨s₀.gpr .rdx, 8 * ((s₀.gpr .rcx).toNat / 8)⟩, ⟨s₀.gpr .r8, 8 * 22⟩]

theorem finalArgs_blk : finalArgs.blk = 8 := rfl

/-- A region of a list, at offset 0 of itself. -/
theorem sub_self_mem {r : Region} {rs : List Region} (h : r ∈ rs) :
    ∃ r' ∈ rs, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len :=
  ⟨r, h, 0, (BitVec.add_zero _).symm, by simp⟩

/-- The first function's precondition, where `cfbFinal` inlines it. -/
theorem call₁_pre {s₀ : State} (hp : finalPre s₀) {u : State} (hu : Call₁ finalArgs s₀ (s₀.gpr .rcx).toNat u) :
    fbPre blkLen (u.withRegions (rdW s₀) (wrW s₀)) ∧ Covers (rdW s₀ ++ wrW s₀) (u.rd ++ u.wr) ∧
      Covers (wrW s₀) u.wr := by
  obtain ⟨⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩, h80, hfr⟩ := hp
  have g0 : u.gpr .rdi = s₀.gpr .rdi := hu.args 0 (by decide) (by decide)
  have g1 : u.gpr .rsi = s₀.gpr .rsi := hu.args 1 (by decide) (by decide)
  have g2 : u.gpr .rdx = s₀.gpr .rdx := hu.args 2 (by decide) (by decide)
  have g4 : u.gpr .r8 = s₀.gpr .r8 := hu.args 4 (by decide) (by decide)
  have hlt : (s₀.gpr .rcx).toNat / 8 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (BitVec.isLt _)
  have hrcx : (u.gpr .rcx).toNat = (s₀.gpr .rcx).toNat / 8 := by
    rw [show u.gpr .rcx = _ from hu.blocks, finalArgs_blk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hsubD : Region.Sub ⟨s₀.gpr .rdx, 8 * ((s₀.gpr .rcx).toNat / 8)⟩ ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩ :=
    Region.sub_prefix (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _)
  have hret : Region.Sub ⟨u.gpr .rsp, 8⟩ (frameRegion s₀) := by
    rw [hu.rsp]; exact Region.sub_prefix (by decide)
  have fr : ∀ r ∈ ([⟨s₀.gpr .rdi, 104⟩, ⟨s₀.gpr .rsi, 8⟩, ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩, ⟨s₀.gpr .r8, 8 * 22⟩] :
      List Region), Region.Disjoint ⟨u.gpr .rsp, 8⟩ r := fun r hr => (hfr r hr).sub_left hret
  have hmul : 8 * ((s₀.gpr .rcx).toNat / 8) ≤ (s₀.gpr .rcx).toNat := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [fbPre, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, blkLen, hrcx, g0, g1, g2,
      g4, rdW, wrW]
    have h1 : (s₀.gpr .rdx).toNat + (s₀.gpr .rcx).toNat ≤ 2 ^ 64 := fitD
    exact ⟨trivial, trivial, dKV, dKD.sub_right hsubD, dKS, dVD.sub_right hsubD, dVS, dDS.sub_left hsubD,
      fr _ (by simp), (fr _ (by simp)).sub_right hsubD, fr _ (by simp), fitK, fitV, by omega, fitB⟩
  · rw [hu.rd, hu.wr, hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [rdW, wrW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sub_self_mem (by simp)
    · exact sub_self_mem (by simp)
    · exact ⟨⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact sub_self_mem (by simp)
  · rw [hu.wr, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [wrW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_self_mem (by simp)
    · exact ⟨⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact sub_self_mem (by simp)

/-- The second function's writable regions: the IV, the working block and
the scratch buffer. -/
def wrE (s₀ : State) : List Region := [⟨s₀.gpr .rsi, 8⟩, ⟨blockAddr s₀, 8⟩, ⟨s₀.gpr .r8, 8 * 22⟩]

theorem blockAddr_eq (s₀ : State) : blockAddr s₀ = s₀.gpr .rsp - BitVec.ofNat 64 80 + BitVec.ofNat 64 8 := by
  rw [blockAddr, sub_add_ofNat _ (by decide)]

/-- The second function's precondition, where `cfbFinal` inlines it. -/
theorem call₂_pre {s₀ : State} (hp : finalPre s₀) {u₁' v u : State}
    (hA : After₁ finalArgs s₀ (s₀.gpr .rcx).toNat cfbEncX86_64 (rdW s₀) (wrW s₀) cfbEncrypt.x86_64Depth u₁' ∨
      After₁ finalArgs s₀ (s₀.gpr .rcx).toNat cfbDecX86_64 (rdW s₀) (wrW s₀) cfbDecrypt.x86_64Depth u₁')
    (vrd : v.rd = u₁'.rd) (vwr : v.wr = u₁'.wr) (hu : Call₂ finalArgs s₀ v u) :
    fbPre blkLen (u.withRegions (rdW s₀) (wrE s₀)) ∧ Covers (rdW s₀ ++ wrE s₀) (u.rd ++ u.wr) ∧
      Covers (wrE s₀) u.wr := by
  obtain ⟨⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩, h80, hfr⟩ := hp
  have hurd : u.rd = s₀.rd := by rw [hu.rd, vrd]; rcases hA with h | h <;> exact h.rd
  have huwr : u.wr = frameRegion s₀ :: s₀.wr := by rw [hu.wr, vwr]; rcases hA with h | h <;> exact h.wr
  have g0 : u.gpr .rdi = s₀.gpr .rdi := hu.args 0 (by decide) (by decide) (by decide)
  have g1 : u.gpr .rsi = s₀.gpr .rsi := hu.args 1 (by decide) (by decide) (by decide)
  have g4 : u.gpr .r8 = s₀.gpr .r8 := hu.args 4 (by decide) (by decide) (by decide)
  have g2 : u.gpr .rdx = blockAddr s₀ := hu.data
  have hrcx : (u.gpr .rcx).toNat = 1 := by rw [show u.gpr .rcx = _ from hu.blocks]; rfl
  have hK : Region.Sub ⟨blockAddr s₀, 8⟩ (frameRegion s₀) := by
    rw [blockAddr_eq, frameRegion]; exact VG.Offset.sub_base _ (by decide)
  have hret : Region.Sub ⟨u.gpr .rsp, 8⟩ (frameRegion s₀) := by
    rw [hu.rsp]; exact Region.sub_prefix (by decide)
  have dRK : Region.Disjoint ⟨u.gpr .rsp, 8⟩ ⟨blockAddr s₀, 8⟩ := by
    rw [hu.rsp, blockAddr_eq]
    have := VG.Offset.disjoint (s₀.gpr .rsp - BitVec.ofNat 64 80) (d := 0) (n := 8) (e := 8) (k := 8)
      (.inl (by decide)) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have fK : ∀ r ∈ ([⟨s₀.gpr .rdi, 104⟩, ⟨s₀.gpr .rsi, 8⟩, ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩, ⟨s₀.gpr .r8, 8 * 22⟩] :
      List Region), Region.Disjoint ⟨blockAddr s₀, 8⟩ r := fun r hr => (hfr r hr).sub_left hK
  have fR : ∀ r ∈ ([⟨s₀.gpr .rdi, 104⟩, ⟨s₀.gpr .rsi, 8⟩, ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩, ⟨s₀.gpr .r8, 8 * 22⟩] :
      List Region), Region.Disjoint ⟨u.gpr .rsp, 8⟩ r := fun r hr => (hfr r hr).sub_left hret
  have hKfit : (blockAddr s₀).toNat + 8 ≤ 2 ^ 64 := by
    rw [blockAddr, toNat_sub_ofNat (by omega)]
    have := (s₀.gpr .rsp).isLt
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [fbPre, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, blkLen, hrcx, g0, g1, g2,
      g4, rdW, wrE]
    exact ⟨trivial, trivial, dKV, (fK _ (by simp)).symm, dKS, (fK _ (by simp)).symm, dVS, fK _ (by simp),
      fR _ (by simp), dRK, fR _ (by simp), fitK, fitV, hKfit, fitB⟩
  · rw [hurd, huwr, hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [rdW, wrE, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sub_self_mem (by simp)
    · exact sub_self_mem (by simp)
    · exact ⟨frameRegion s₀, by simp, 8, blockAddr_eq s₀, show 8 + 8 ≤ 80 by decide⟩
    · exact sub_self_mem (by simp)
  · rw [huwr, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [wrE, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_self_mem (by simp)
    · exact ⟨frameRegion s₀, by simp, 8, blockAddr_eq s₀, show 8 + 8 ≤ 80 by decide⟩
    · exact sub_self_mem (by simp)

end VG.Proof.Idea.X86_64
