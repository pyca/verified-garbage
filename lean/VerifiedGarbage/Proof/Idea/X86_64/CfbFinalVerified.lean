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
import VerifiedGarbage.Proof.Framework.Mem
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
open VG.Proof.Modes.X86_64 (FinalOk Call₁ Call₂ After₁ After₂ FinalDone frameRegion blockAddr slotsRegion frameSp
  sub_add_ofNat restAddr slots_sub_frame block_slots disjoint_empty cfbFinal_wp)
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

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem blocksOf_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 8 * n⟩ : Region).Disjoint r) :
    Modes.blocksOf 8 m' p n = Modes.blocksOf 8 m p n := by
  simp only [Modes.blocksOf]
  refine List.map_congr_left fun i hi => bytesAt_frame hf (fun r hr => (hd r hr).sub_left
    (VG.Offset.sub_base p (by have := List.mem_range.mp hi; omega))) (by decide)

theorem cipher_length (k : Spec.Idea.Schedule) (b : List Byte) : (Spec.Idea.cipher k b).length = 8 := by
  simp [Spec.Idea.cipher]

theorem cfbEncrypt_depth : cfbEncrypt.x86_64Depth = 0 := by lit_decide

theorem cfbDecrypt_depth : cfbDecrypt.x86_64Depth = 0 := by lit_decide

/-- A quadword that reads zero holds eight zero bytes. -/
theorem bytes_zero {m : Mem} {a : Addr} (h : m.readW a 64 = 0) : bytesAt m a 8 = List.replicate 8 0 := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  have hi : i < 8 := by simpa [bytesAt] using h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  rw [← Mem.extractLsb'_read m a hi]
  have : (m.read a 8) = (m.readW a 64) := by simp [Mem.readW]
  rw [this, h]
  simp

/-- CFB encryption of a zero block: the cipher of the IV. -/
theorem encrypt_zero (k : Spec.Idea.Schedule) (c : List Byte) :
    Spec.Cfb.encrypt (Spec.Idea.cipher k) c [List.replicate 8 0] = [Spec.Idea.cipher k c] := by
  simp only [Spec.Cfb.encrypt, List.cons.injEq, and_true]
  apply List.ext_getElem (by simp [Spec.Cbc.xor, cipher_length])
  intro i h1 h2
  simp only [Spec.Cbc.xor, List.getElem_zipWith, List.getElem_replicate]
  exact BitVec.zero_xor

/-- The final functions' contract on x86-64: `finalPre`, and the data and
the IV as `Spec.Cfb.EncryptFinal` says. -/
def cfbEncFinalX86_64 : Contract isa where
  pre := finalPre
  post s s' := Spec.Cfb.EncryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx).toNat
  pub := fbPub

theorem cfbEncrypt_correct (s : State) (hs : cfbEncX86_64.pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ cfbEncX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cfbEncrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncrypt) (by lit_decide) he hg, hpost⟩

theorem cfbEncrypt_spSafe : SpSafe cfbEncrypt := SpSafe.of_all (Code.all_of_allInstrs (by lit_decide))

/-- `vg_idea_cfb64_encrypt_final` on x86-64. -/
theorem cfbEncryptFinal_wp {s₀ : State} (hp : finalPre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncFinalX86_64.post s₀ s' := by
  have hp' := hp
  obtain ⟨⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩, h80, hfr⟩ := hp'
  have fitD' : (s₀.gpr .rdx).toNat + (s₀.gpr .rcx).toNat ≤ 2 ^ 64 := fitD
  have hlen := (s₀.gpr .rcx).isLt
  have hmul : 8 * ((s₀.gpr .rcx).toNat / 8) ≤ (s₀.gpr .rcx).toNat := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hsubD : Region.Sub ⟨s₀.gpr .rdx, 8 * ((s₀.gpr .rcx).toNat / 8)⟩ ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩ :=
    Region.sub_prefix hmul
  have fK : ∀ r ∈ ([⟨s₀.gpr .rdi, 104⟩, ⟨s₀.gpr .rsi, 8⟩, ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩, ⟨s₀.gpr .r8, 8 * 22⟩] :
      List Region), Region.Disjoint (slotsRegion s₀) r := fun r hr => (hfr r hr).sub_left (slots_sub_frame s₀)
  have slotsW : ∀ r ∈ wrW s₀, r.Disjoint (slotsRegion s₀) := by
    intro r hr
    simp only [wrW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (fK _ (by simp)).symm
    · exact ((fK _ (by simp)).sub_right hsubD).symm
    · exact (fK _ (by simp)).symm
  have slotsE : ∀ r ∈ wrE s₀, r.Disjoint (slotsRegion s₀) := by
    intro r hr
    simp only [wrE, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (fK _ (by simp)).symm
    · exact block_slots s₀ (by decide)
    · exact (fK _ (by simp)).symm
  have hL : s₀.gpr (finalArgs.arg finalArgs.lenIx) = BitVec.ofNat 64 (s₀.gpr .rcx).toNat :=
    (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
  refine WP.mono (cfbFinal_wp finalArgs_ok cfbEncrypt_correct cfbEncrypt_correct cfbEncrypt_spSafe cfbEncrypt_spSafe
    (by rw [cfbEncrypt_depth]; decide) (by rw [cfbEncrypt_depth]; decide) (D := s₀.gpr .rdx) rfl hL hlen h80
    (by rw [hwr]; simp) fitD' (hfr _ (by simp)).symm (fun u hu => call₁_pre hp hu) slotsW
    (rdE := rdW s₀) (wrE := wrE s₀)
    (fun u₁' v u hA _ vrd vwr hu => call₂_pre hp (.inl hA) vrd vwr hu) slotsE) fun s' d => ?_
  rw [cfbEncrypt_depth] at d
  have retF : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ (frameRegion s₀) :=
    VG.Offset.base_disjoint_below _ (by decide)
  have dSF : Region.Disjoint ⟨s₀.gpr .rdi, 104⟩ (frameRegion s₀) := (hfr _ (by simp)).symm
  have dVF : Region.Disjoint ⟨s₀.gpr .rsi, 8⟩ (frameRegion s₀) := (hfr _ (by simp)).symm
  have dDF : Region.Disjoint ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩ (frameRegion s₀) := (hfr _ (by simp)).symm
  have dBF : Region.Disjoint ⟨s₀.gpr .r8, 8 * 22⟩ (frameRegion s₀) := (hfr _ (by simp)).symm
  have hKF : Region.Sub ⟨blockAddr s₀, 8⟩ (frameRegion s₀) := by
    rw [blockAddr_eq, frameRegion]; exact VG.Offset.sub_base _ (by decide)
  refine ⟨⟨d.cs, ?_⟩, ?_⟩
  · -- The return address.
    refine (d.frame finalArgs_ok).readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [wrW, wrE, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact retF
    · exact disjoint_empty _ _
    · exact disjoint_empty _ _
    · exact dRD
    · exact dRV
    · exact dRD.sub_right hsubD
    · exact dRS
    · exact dRV
    · exact retF.sub_right hKF
    · exact dRS
  · -- The first function's results, in terms of `s₀`.
    obtain ⟨u₁', hA, h0, h1⟩ := d.run
    obtain ⟨u₁, hu₁, post₁, f₁⟩ := hA.run
    have g0 : u₁.gpr .rdi = s₀.gpr .rdi := hu₁.args 0 (by decide) (by decide)
    have g1 : u₁.gpr .rsi = s₀.gpr .rsi := hu₁.args 1 (by decide) (by decide)
    have g2 : u₁.gpr .rdx = s₀.gpr .rdx := hu₁.args 2 (by decide) (by decide)
    have hlt : (s₀.gpr .rcx).toNat / 8 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlen
    have g3 : (u₁.gpr .rcx).toNat = (s₀.gpr .rcx).toNat / 8 := by
      rw [show u₁.gpr .rcx = _ from hu₁.blocks, finalArgs_blk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have one : ∀ {X : Region}, X.Disjoint (frameRegion s₀) → ∀ r ∈ [frameRegion s₀], X.Disjoint r := fun h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h
    have sch₁ : Spec.Idea.scheduleAt u₁.mem (s₀.gpr .rdi) = Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi) :=
      scheduleAt_frame hu₁.frame (one dSF)
    have iv₁ : bytesAt u₁.mem (s₀.gpr .rsi) 8 = bytesAt s₀.mem (s₀.gpr .rsi) 8 := bytesAt_frame hu₁.frame (one dVF) (by decide)
    have bl₁ : Modes.blocksOf 8 u₁.mem (s₀.gpr .rdx) ((s₀.gpr .rcx).toNat / 8) =
        Modes.blocksOf 8 s₀.mem (s₀.gpr .rdx) ((s₀.gpr .rcx).toNat / 8) :=
      blocksOf_frame hu₁.frame (one (dDF.sub_left hsubD))
    obtain ⟨H1, H2⟩ := post₁
    simp only [blocksOf, ciphOf, ivOf, State.withRegions_gpr, State.withRegions_mem, g0, g1, g2, g3, sch₁, iv₁,
      cbcBlocksAt_eq, bl₁] at H1 H2
    unfold cfbEncFinalX86_64 Spec.Cfb.EncryptFinal
    simp only [ciphOf]
    by_cases hr : (s₀.gpr .rcx).toNat % 8 = 0
    · -- No partial last segment.
      have hs' : s'.mem = u₁'.mem := h0 (by rw [finalArgs_blk]; exact hr)
      refine ⟨?_, ?_⟩
      · rw [hs']
        refine Modes.cfbEncFinal_of _ _ _ _ _ _ H1 ?_
        rw [hr]; rfl
      · rw [hs', H2, ← Modes.cfbEncFinalNext_of, ite_eq_left hr]
    · -- A partial last segment.
      obtain ⟨v, u₂', vm, vrd, vwr, -, hA₂, hx, f₃⟩ := h1 (by rw [finalArgs_blk]; exact hr)
      obtain ⟨u₂, hu₂, post₂, f₂⟩ := hA₂.run
      rw [finalArgs_blk] at hx f₃
      have hlen8 : 8 * ((s₀.gpr .rcx).toNat / 8) + (s₀.gpr .rcx).toNat % 8 = (s₀.gpr .rcx).toNat :=
        Nat.div_add_mod _ _
      have hr8 : (s₀.gpr .rcx).toNat % 8 < 8 := Nat.mod_lt _ (by decide)
      -- Regions.
      have hRsub : Region.Sub ⟨restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat, (s₀.gpr .rcx).toNat % 8⟩
          ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩ := VG.Offset.sub_base _ (by rw [finalArgs_blk]; omega)
      have dWR : Region.Disjoint ⟨s₀.gpr .rdx, 8 * ((s₀.gpr .rcx).toNat / 8)⟩
          ⟨restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat, (s₀.gpr .rcx).toNat % 8⟩ :=
        VG.Offset.base_disjoint _ (by rw [finalArgs_blk]) (by rw [finalArgs_blk]; omega)
      have dRV' := (dVD.sub_right hRsub)
      have dRS' := (dDS.sub_left hRsub)
      have dRF := (dDF.sub_left hRsub)
      have dKK : Region.Disjoint ⟨s₀.gpr .rdi, 104⟩ ⟨blockAddr s₀, 8⟩ := dSF.sub_right hKF
      have dKV' : Region.Disjoint ⟨s₀.gpr .rsi, 8⟩ ⟨blockAddr s₀, 8⟩ := dVF.sub_right hKF
      -- The second function's results.
      have q0 : u₂.gpr .rdi = s₀.gpr .rdi := hu₂.args 0 (by decide) (by decide) (by decide)
      have q1 : u₂.gpr .rsi = s₀.gpr .rsi := hu₂.args 1 (by decide) (by decide) (by decide)
      have q2 : u₂.gpr .rdx = blockAddr s₀ := hu₂.data
      have q3 : (u₂.gpr .rcx).toNat = 1 := by rw [show u₂.gpr .rcx = _ from hu₂.blocks]; rfl
      have memb : ∀ {X : Region} {rs : List Region}, (∀ r ∈ rs, X.Disjoint r) → ∀ r ∈ rs, X.Disjoint r := id
      have dW1 : ∀ {X : Region}, X.Disjoint ⟨s₀.gpr .rsi, 8⟩ → X.Disjoint ⟨s₀.gpr .rdx, 8 * ((s₀.gpr .rcx).toNat / 8)⟩ →
          X.Disjoint ⟨s₀.gpr .r8, 8 * 22⟩ → ∀ r ∈ wrW s₀ ++ [below (frameSp s₀) 0], X.Disjoint r :=
        fun h1 h2 h3 r hr => by
          simp only [wrW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          exacts [h1, h2, h3, disjoint_empty _ _]
      have dE1 : ∀ {X : Region}, X.Disjoint ⟨s₀.gpr .rsi, 8⟩ → X.Disjoint ⟨blockAddr s₀, 8⟩ →
          X.Disjoint ⟨s₀.gpr .r8, 8 * 22⟩ → ∀ r ∈ wrE s₀ ++ [below (frameSp s₀) 0], X.Disjoint r :=
        fun h1 h2 h3 r hr => by
          simp only [wrE, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          exacts [h1, h2, h3, disjoint_empty _ _]
      have oneK : ∀ {X : Region}, X.Disjoint ⟨blockAddr s₀, 8⟩ → ∀ r ∈ [(⟨blockAddr s₀, 8⟩ : Region)], X.Disjoint r :=
        fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h
      have sch₂ : Spec.Idea.scheduleAt u₂.mem (s₀.gpr .rdi) = Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi) := by
        rw [scheduleAt_frame hu₂.frame (oneK dKK), vm, scheduleAt_frame f₁ (dW1 dKV (dKD.sub_right hsubD) dKS), sch₁]
      have iv₂ : bytesAt u₂.mem (s₀.gpr .rsi) 8 = bytesAt u₁'.mem (s₀.gpr .rsi) 8 := by
        rw [bytesAt_frame hu₂.frame (oneK dKV') (by decide), vm]
      have blk₂ : Modes.blocksOf 8 u₂.mem (blockAddr s₀) 1 = [List.replicate 8 0] := by
        have := hu₂.zero 0 (by rw [finalArgs_blk]; decide)
        simp only [Modes.blocksOf, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero] at this ⊢
        rw [bytes_zero this]
      obtain ⟨H3, H4⟩ := post₂
      simp only [blocksOf, ciphOf, ivOf, State.withRegions_gpr, State.withRegions_mem, q0, q1, q2, q3, sch₂, iv₂,
        H2, cbcBlocksAt_eq, blk₂, encrypt_zero] at H3 H4
      have K₂ : bytesAt u₂'.mem (blockAddr s₀) 8 =
          Spec.Idea.cipher (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi))
            (Spec.Cbc.next (bytesAt s₀.mem (s₀.gpr .rsi) 8)
              (Spec.Cfb.encrypt (Spec.Idea.cipher (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi)))
                (bytesAt s₀.mem (s₀.gpr .rsi) 8) (Modes.blocksOf 8 s₀.mem (s₀.gpr .rdx) ((s₀.gpr .rcx).toNat / 8)))) := by
        simp only [Modes.blocksOf, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
          List.cons.injEq, and_true] at H3
        exact H3
      have dWK : Region.Disjoint ⟨s₀.gpr .rdx, 8 * ((s₀.gpr .rcx).toNat / 8)⟩ ⟨blockAddr s₀, 8⟩ :=
        (dDF.sub_left hsubD).sub_right hKF
      have dRK : Region.Disjoint ⟨restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat, (s₀.gpr .rcx).toNat % 8⟩
          ⟨blockAddr s₀, 8⟩ := dRF.sub_right hKF
      have two : ∀ {X : Region}, X.Disjoint ⟨restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat, (s₀.gpr .rcx).toNat % 8⟩ →
          X.Disjoint ⟨blockAddr s₀, 8⟩ → ∀ r ∈ [(⟨restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat,
            (s₀.gpr .rcx).toNat % 8⟩ : Region), ⟨blockAddr s₀, 8⟩], X.Disjoint r := fun h1 h2 r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [h1, h2]
      -- The rest's bytes on entry, where the second function left them.
      have rest₂ : bytesAt u₂'.mem (restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat) ((s₀.gpr .rcx).toNat % 8) =
          bytesAt s₀.mem (restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat) ((s₀.gpr .rcx).toNat % 8) := by
        rw [bytesAt_frame f₂ (dE1 dRV'.symm dRK dRS') (by omega), bytesAt_frame hu₂.frame (oneK dRK) (by omega), vm,
          bytesAt_frame f₁ (dW1 dRV'.symm dWR.symm dRS') (by omega),
          bytesAt_frame hu₁.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dRF) (by omega)]
      refine ⟨Modes.cfbEncFinal_of _ _ _ _ _ _ ?_ ?_, ?_⟩
      · rw [blocksOf_frame f₃ (two dWR dWK), blocksOf_frame f₂ (dE1 (dVD.sub_right hsubD).symm dWK
          (dDS.sub_left hsubD)), blocksOf_frame hu₂.frame (oneK dWK), vm]
        exact H1
      · apply List.ext_getElem (by simp [bytesAt, Spec.Cbc.xor, cipher_length]; omega)
        intro q h1 h2
        have hq : q < (s₀.gpr .rcx).toNat % 8 := by simpa [bytesAt] using h1
        have e1 := hx q hq
        have e2 := congrArg (fun l => l[q]?) rest₂
        have e3 := congrArg (fun l => l[q]?) K₂
        simp only [bytesAt, List.getElem?_map, List.getElem?_range, hq, Option.map_some,
          show q < 8 by omega, Option.some.injEq] at e2 e3
        rw [List.getElem?_eq_getElem (by rw [cipher_length]; omega), Option.some.injEq] at e3
        simp only [bytesAt, List.getElem_map, List.getElem_range, Spec.Cbc.xor, List.getElem_zipWith]
        rw [← e3]
        exact e1.trans (congrArg (· ^^^ u₂'.mem (blockAddr s₀ + BitVec.ofNat 64 q)) e2)
      · rw [bytesAt_frame f₃ (two (dVD.sub_right hRsub) dKV') (by decide), H4, ← Modes.cfbEncFinalNext_of,
          ite_eq_right hr]
        rfl


theorem cfbDecrypt_correct (s : State) (hs : cfbDecX86_64.pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ cfbDecX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cfbDecrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecrypt) (by lit_decide) he hg, hpost⟩

theorem cfbDecrypt_spSafe : SpSafe cfbDecrypt := SpSafe.of_all (Code.all_of_allInstrs (by lit_decide))

/-- The final decryption's contract on x86-64: `finalPre`, and the data and
the IV as `Spec.Cfb.DecryptFinal` says. -/
def cfbDecFinalX86_64 : Contract isa where
  pre := finalPre
  post s s' := Spec.Cfb.DecryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx).toNat
  pub := fbPub

/-- `vg_idea_cfb64_decrypt_final` on x86-64. -/
theorem cfbDecryptFinal_wp {s₀ : State} (hp : finalPre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecFinalX86_64.post s₀ s' := by
  have hp' := hp
  obtain ⟨⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩, h80, hfr⟩ := hp'
  have fitD' : (s₀.gpr .rdx).toNat + (s₀.gpr .rcx).toNat ≤ 2 ^ 64 := fitD
  have hlen := (s₀.gpr .rcx).isLt
  have hmul : 8 * ((s₀.gpr .rcx).toNat / 8) ≤ (s₀.gpr .rcx).toNat := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hsubD : Region.Sub ⟨s₀.gpr .rdx, 8 * ((s₀.gpr .rcx).toNat / 8)⟩ ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩ :=
    Region.sub_prefix hmul
  have fK : ∀ r ∈ ([⟨s₀.gpr .rdi, 104⟩, ⟨s₀.gpr .rsi, 8⟩, ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩, ⟨s₀.gpr .r8, 8 * 22⟩] :
      List Region), Region.Disjoint (slotsRegion s₀) r := fun r hr => (hfr r hr).sub_left (slots_sub_frame s₀)
  have slotsW : ∀ r ∈ wrW s₀, r.Disjoint (slotsRegion s₀) := by
    intro r hr
    simp only [wrW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (fK _ (by simp)).symm
    · exact ((fK _ (by simp)).sub_right hsubD).symm
    · exact (fK _ (by simp)).symm
  have slotsE : ∀ r ∈ wrE s₀, r.Disjoint (slotsRegion s₀) := by
    intro r hr
    simp only [wrE, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (fK _ (by simp)).symm
    · exact block_slots s₀ (by decide)
    · exact (fK _ (by simp)).symm
  have hL : s₀.gpr (finalArgs.arg finalArgs.lenIx) = BitVec.ofNat 64 (s₀.gpr .rcx).toNat :=
    (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
  refine WP.mono (cfbFinal_wp finalArgs_ok cfbDecrypt_correct cfbEncrypt_correct cfbDecrypt_spSafe cfbEncrypt_spSafe
    (by rw [cfbDecrypt_depth]; decide) (by rw [cfbEncrypt_depth]; decide) (D := s₀.gpr .rdx) rfl hL hlen h80
    (by rw [hwr]; simp) fitD' (hfr _ (by simp)).symm (fun u hu => call₁_pre hp hu) slotsW
    (rdE := rdW s₀) (wrE := wrE s₀)
    (fun u₁' v u hA _ vrd vwr hu => call₂_pre hp (.inr hA) vrd vwr hu) slotsE) fun s' d => ?_
  rw [cfbDecrypt_depth, cfbEncrypt_depth] at d
  have retF : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ (frameRegion s₀) :=
    VG.Offset.base_disjoint_below _ (by decide)
  have dSF : Region.Disjoint ⟨s₀.gpr .rdi, 104⟩ (frameRegion s₀) := (hfr _ (by simp)).symm
  have dVF : Region.Disjoint ⟨s₀.gpr .rsi, 8⟩ (frameRegion s₀) := (hfr _ (by simp)).symm
  have dDF : Region.Disjoint ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩ (frameRegion s₀) := (hfr _ (by simp)).symm
  have dBF : Region.Disjoint ⟨s₀.gpr .r8, 8 * 22⟩ (frameRegion s₀) := (hfr _ (by simp)).symm
  have hKF : Region.Sub ⟨blockAddr s₀, 8⟩ (frameRegion s₀) := by
    rw [blockAddr_eq, frameRegion]; exact VG.Offset.sub_base _ (by decide)
  refine ⟨⟨d.cs, ?_⟩, ?_⟩
  · -- The return address.
    refine (d.frame finalArgs_ok).readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [wrW, wrE, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact retF
    · exact disjoint_empty _ _
    · exact disjoint_empty _ _
    · exact dRD
    · exact dRV
    · exact dRD.sub_right hsubD
    · exact dRS
    · exact dRV
    · exact retF.sub_right hKF
    · exact dRS
  · -- The first function's results, in terms of `s₀`.
    obtain ⟨u₁', hA, h0, h1⟩ := d.run
    obtain ⟨u₁, hu₁, post₁, f₁⟩ := hA.run
    have g0 : u₁.gpr .rdi = s₀.gpr .rdi := hu₁.args 0 (by decide) (by decide)
    have g1 : u₁.gpr .rsi = s₀.gpr .rsi := hu₁.args 1 (by decide) (by decide)
    have g2 : u₁.gpr .rdx = s₀.gpr .rdx := hu₁.args 2 (by decide) (by decide)
    have hlt : (s₀.gpr .rcx).toNat / 8 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlen
    have g3 : (u₁.gpr .rcx).toNat = (s₀.gpr .rcx).toNat / 8 := by
      rw [show u₁.gpr .rcx = _ from hu₁.blocks, finalArgs_blk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have one : ∀ {X : Region}, X.Disjoint (frameRegion s₀) → ∀ r ∈ [frameRegion s₀], X.Disjoint r := fun h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h
    have sch₁ : Spec.Idea.scheduleAt u₁.mem (s₀.gpr .rdi) = Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi) :=
      scheduleAt_frame hu₁.frame (one dSF)
    have iv₁ : bytesAt u₁.mem (s₀.gpr .rsi) 8 = bytesAt s₀.mem (s₀.gpr .rsi) 8 := bytesAt_frame hu₁.frame (one dVF) (by decide)
    have bl₁ : Modes.blocksOf 8 u₁.mem (s₀.gpr .rdx) ((s₀.gpr .rcx).toNat / 8) =
        Modes.blocksOf 8 s₀.mem (s₀.gpr .rdx) ((s₀.gpr .rcx).toNat / 8) :=
      blocksOf_frame hu₁.frame (one (dDF.sub_left hsubD))
    obtain ⟨H1, H2⟩ := post₁
    simp only [blocksOf, ciphOf, ivOf, State.withRegions_gpr, State.withRegions_mem, g0, g1, g2, g3, sch₁, iv₁,
      cbcBlocksAt_eq, bl₁] at H1 H2
    unfold cfbDecFinalX86_64 Spec.Cfb.DecryptFinal
    simp only [ciphOf]
    by_cases hr : (s₀.gpr .rcx).toNat % 8 = 0
    · -- No partial last segment.
      have hs' : s'.mem = u₁'.mem := h0 (by rw [finalArgs_blk]; exact hr)
      refine ⟨?_, ?_⟩
      · rw [hs']
        refine Modes.cfbDecFinal_of _ _ _ _ _ _ H1 ?_
        rw [hr]; rfl
      · rw [hs', H2, ← Modes.cfbDecFinalNext_of, ite_eq_left hr]
    · -- A partial last segment.
      obtain ⟨v, u₂', vm, vrd, vwr, -, hA₂, hx, f₃⟩ := h1 (by rw [finalArgs_blk]; exact hr)
      obtain ⟨u₂, hu₂, post₂, f₂⟩ := hA₂.run
      rw [finalArgs_blk] at hx f₃
      have hlen8 : 8 * ((s₀.gpr .rcx).toNat / 8) + (s₀.gpr .rcx).toNat % 8 = (s₀.gpr .rcx).toNat :=
        Nat.div_add_mod _ _
      have hr8 : (s₀.gpr .rcx).toNat % 8 < 8 := Nat.mod_lt _ (by decide)
      -- Regions.
      have hRsub : Region.Sub ⟨restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat, (s₀.gpr .rcx).toNat % 8⟩
          ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩ := VG.Offset.sub_base _ (by rw [finalArgs_blk]; omega)
      have dWR : Region.Disjoint ⟨s₀.gpr .rdx, 8 * ((s₀.gpr .rcx).toNat / 8)⟩
          ⟨restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat, (s₀.gpr .rcx).toNat % 8⟩ :=
        VG.Offset.base_disjoint _ (by rw [finalArgs_blk]) (by rw [finalArgs_blk]; omega)
      have dRV' := (dVD.sub_right hRsub)
      have dRS' := (dDS.sub_left hRsub)
      have dRF := (dDF.sub_left hRsub)
      have dKK : Region.Disjoint ⟨s₀.gpr .rdi, 104⟩ ⟨blockAddr s₀, 8⟩ := dSF.sub_right hKF
      have dKV' : Region.Disjoint ⟨s₀.gpr .rsi, 8⟩ ⟨blockAddr s₀, 8⟩ := dVF.sub_right hKF
      -- The second function's results.
      have q0 : u₂.gpr .rdi = s₀.gpr .rdi := hu₂.args 0 (by decide) (by decide) (by decide)
      have q1 : u₂.gpr .rsi = s₀.gpr .rsi := hu₂.args 1 (by decide) (by decide) (by decide)
      have q2 : u₂.gpr .rdx = blockAddr s₀ := hu₂.data
      have q3 : (u₂.gpr .rcx).toNat = 1 := by rw [show u₂.gpr .rcx = _ from hu₂.blocks]; rfl
      have memb : ∀ {X : Region} {rs : List Region}, (∀ r ∈ rs, X.Disjoint r) → ∀ r ∈ rs, X.Disjoint r := id
      have dW1 : ∀ {X : Region}, X.Disjoint ⟨s₀.gpr .rsi, 8⟩ → X.Disjoint ⟨s₀.gpr .rdx, 8 * ((s₀.gpr .rcx).toNat / 8)⟩ →
          X.Disjoint ⟨s₀.gpr .r8, 8 * 22⟩ → ∀ r ∈ wrW s₀ ++ [below (frameSp s₀) 0], X.Disjoint r :=
        fun h1 h2 h3 r hr => by
          simp only [wrW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          exacts [h1, h2, h3, disjoint_empty _ _]
      have dE1 : ∀ {X : Region}, X.Disjoint ⟨s₀.gpr .rsi, 8⟩ → X.Disjoint ⟨blockAddr s₀, 8⟩ →
          X.Disjoint ⟨s₀.gpr .r8, 8 * 22⟩ → ∀ r ∈ wrE s₀ ++ [below (frameSp s₀) 0], X.Disjoint r :=
        fun h1 h2 h3 r hr => by
          simp only [wrE, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          exacts [h1, h2, h3, disjoint_empty _ _]
      have oneK : ∀ {X : Region}, X.Disjoint ⟨blockAddr s₀, 8⟩ → ∀ r ∈ [(⟨blockAddr s₀, 8⟩ : Region)], X.Disjoint r :=
        fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h
      have sch₂ : Spec.Idea.scheduleAt u₂.mem (s₀.gpr .rdi) = Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi) := by
        rw [scheduleAt_frame hu₂.frame (oneK dKK), vm, scheduleAt_frame f₁ (dW1 dKV (dKD.sub_right hsubD) dKS), sch₁]
      have iv₂ : bytesAt u₂.mem (s₀.gpr .rsi) 8 = bytesAt u₁'.mem (s₀.gpr .rsi) 8 := by
        rw [bytesAt_frame hu₂.frame (oneK dKV') (by decide), vm]
      have blk₂ : Modes.blocksOf 8 u₂.mem (blockAddr s₀) 1 = [List.replicate 8 0] := by
        have := hu₂.zero 0 (by rw [finalArgs_blk]; decide)
        simp only [Modes.blocksOf, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero] at this ⊢
        rw [bytes_zero this]
      obtain ⟨H3, H4⟩ := post₂
      simp only [blocksOf, ciphOf, ivOf, State.withRegions_gpr, State.withRegions_mem, q0, q1, q2, q3, sch₂, iv₂,
        H2, cbcBlocksAt_eq, blk₂, encrypt_zero] at H3 H4
      have K₂ : bytesAt u₂'.mem (blockAddr s₀) 8 =
          Spec.Idea.cipher (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi))
            (Spec.Cbc.next (bytesAt s₀.mem (s₀.gpr .rsi) 8)
              (Modes.blocksOf 8 s₀.mem (s₀.gpr .rdx) ((s₀.gpr .rcx).toNat / 8))) := by
        simp only [Modes.blocksOf, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
          List.cons.injEq, and_true] at H3
        exact H3
      have dWK : Region.Disjoint ⟨s₀.gpr .rdx, 8 * ((s₀.gpr .rcx).toNat / 8)⟩ ⟨blockAddr s₀, 8⟩ :=
        (dDF.sub_left hsubD).sub_right hKF
      have dRK : Region.Disjoint ⟨restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat, (s₀.gpr .rcx).toNat % 8⟩
          ⟨blockAddr s₀, 8⟩ := dRF.sub_right hKF
      have two : ∀ {X : Region}, X.Disjoint ⟨restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat, (s₀.gpr .rcx).toNat % 8⟩ →
          X.Disjoint ⟨blockAddr s₀, 8⟩ → ∀ r ∈ [(⟨restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat,
            (s₀.gpr .rcx).toNat % 8⟩ : Region), ⟨blockAddr s₀, 8⟩], X.Disjoint r := fun h1 h2 r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [h1, h2]
      -- The rest's bytes on entry, where the second function left them.
      have rest₂ : bytesAt u₂'.mem (restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat) ((s₀.gpr .rcx).toNat % 8) =
          bytesAt s₀.mem (restAddr finalArgs (s₀.gpr .rdx) (s₀.gpr .rcx).toNat) ((s₀.gpr .rcx).toNat % 8) := by
        rw [bytesAt_frame f₂ (dE1 dRV'.symm dRK dRS') (by omega), bytesAt_frame hu₂.frame (oneK dRK) (by omega), vm,
          bytesAt_frame f₁ (dW1 dRV'.symm dWR.symm dRS') (by omega),
          bytesAt_frame hu₁.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dRF) (by omega)]
      refine ⟨Modes.cfbDecFinal_of _ _ _ _ _ _ ?_ ?_, ?_⟩
      · rw [blocksOf_frame f₃ (two dWR dWK), blocksOf_frame f₂ (dE1 (dVD.sub_right hsubD).symm dWK
          (dDS.sub_left hsubD)), blocksOf_frame hu₂.frame (oneK dWK), vm]
        exact H1
      · apply List.ext_getElem (by simp [bytesAt, Spec.Cbc.xor, cipher_length]; omega)
        intro q h1 h2
        have hq : q < (s₀.gpr .rcx).toNat % 8 := by simpa [bytesAt] using h1
        have e1 := hx q hq
        have e2 := congrArg (fun l => l[q]?) rest₂
        have e3 := congrArg (fun l => l[q]?) K₂
        simp only [bytesAt, List.getElem?_map, List.getElem?_range, hq, Option.map_some,
          show q < 8 by omega, Option.some.injEq] at e2 e3
        rw [List.getElem?_eq_getElem (by rw [cipher_length]; omega), Option.some.injEq] at e3
        simp only [bytesAt, List.getElem_map, List.getElem_range, Spec.Cbc.xor, List.getElem_zipWith]
        rw [← e3]
        exact e1.trans (congrArg (· ^^^ u₂'.mem (blockAddr s₀ + BitVec.ofNat 64 q)) e2)
      · rw [bytesAt_frame f₃ (two (dVD.sub_right hRsub) dKV') (by decide), H4, ← Modes.cfbDecFinalNext_of,
          ite_eq_right hr]
        rfl

end VG.Proof.Idea.X86_64
