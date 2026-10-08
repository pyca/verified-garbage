import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Cipher
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Data
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Memory
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Bump

/-! # One complete eight-block pipeline batch -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs batch xorData)
open VG.Spec.Gcm (Block inc32 blockAt)
open VG.Proof.Gcm.X86_64.Pclmul (reduceB)
open VG.Proof.Gcm.X86_64 (revMask)

def batchR (s : State) (j : Nat) : Region :=
  ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 128⟩

structure BatchPost (s₀ start : State) (P X Y : Nat → Block) (y : Block)
    (c j : Nat) (hashing : Bool) (s : State) : Prop where
  env : Env s₀ P s
  templates : Templates s₀ (c + 8) 0 s.mem
  prepared : Prepared s₀ X Y (if hashing then 8 else 0) s.mem
  hash : s.lane .xmm2 0 = if hashing then reduceB (accN X P y 8) else y
  data : ∀ k < 8, blockAt s.mem (start.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
    blockAt start.mem (start.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) ^^^
      ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀))
  frame : Frame [batchR start j, workR s₀] start.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .r8 → s.gpr r = start.gpr r
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 16)

private theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem batch_ok {s₀ s : State} {P X Y : Nat → Block} {y : Block} {c : Nat}
    (hp : SPre s₀) (hashing more : Bool) (j : Nat) (hE : Env s₀ P s)
    (hT : Templates s₀ c 0 s.mem) (hB : Prepared s₀ X Y 0 s.mem) (hy : s.lane .xmm2 0 = y)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hw : ∀ k < 8, InRegions s₀.wr (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) 16)
    (hwrap : (s.gpr .rdx).toNat + 16 * (j + 8) ≤ 2 ^ 64)
    (hsub : Region.Sub (batchR s j) (dR s₀))
    (hr : hashing = true → more = true → ∀ k < 16, InRegions (s₀.rd ++ s₀.wr)
      (s.gpr .rdx + BitVec.ofNat 64 (16 * k)) 16)
    (hs : hashing = true → more = true → ∀ k < 16, Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * k), 16⟩ (pR s₀))
    (hx : hashing = true → more = true → ∀ k < 16, blockAt s.mem
      (s.gpr .rdx + BitVec.ofNat 64 (16 * k)) = X k)
    (hY : hashing = true → ∀ i < 8, Y i = if more then X (8 + i) else X i) :
    WP isa (batch (nr s₀) 8 j (fun r => if hashing then
      VG.Impl.Gcm.X86_64.StitchAvx8.q8 (nr s₀) more r else [])) s
      (BatchPost s₀ s P X Y y c j hashing) := by
  have hsep : (batchR s j).Disjoint (pR s₀) := hp.d_p.sub_left hsub
  simp only [batch, show aregs.take 8 = aregs from rfl]
  apply seq_assoc
  refine WP.seq (WP.mono (cipherBatch_ok hp hashing more hE hT hB hy hv hr hs hx hY)
    fun t ⟨hks, ht⟩ => ?_)
  rw [WP.block_append_iff]
  have hrdx : t.gpr .rdx = s.gpr .rdx := ht.regs _ (by decide)
  refine WP.mono (xorData_ok aregs j t (by decide) (fun k hk => by
    rw [ht.env.wr, hrdx, BitVec.ofInt_natCast]; exact hw k hk)
    (by rw [hrdx]; exact hwrap)) fun u ⟨hdata, hm, hg, hrd, hwr, hlanes⟩ => ?_
  rw [hrdx] at hdata hm
  have hmD : Frame [dR s₀] t.mem u.mem := hm.sub fun r hr' => by
    simp only [List.mem_singleton] at hr'
    subst r
    exact ⟨dR s₀, List.mem_singleton_self _, hsub⟩
  have hEu := ht.env.writeData hp hg hrd hwr hmD
  have hTu : Templates s₀ (c + 8) 0 u.mem := ht.templates.next.frame hm (by
    intro r hr'; simp only [List.mem_singleton] at hr'; subst r
    exact hsep.symm.sub_left (Offset.sub_base (pp s₀) (d := 640) (n := 128) (k := 1024) (by decide)))
  have hBu := ht.prepared.frame hm (by
    intro r hr'; simp only [List.mem_singleton] at hr'; subst r
    exact hsep.symm.sub_left (Offset.sub_base (pp s₀) (d := 512) (n := 128) (k := 1024) (by decide)))
  have hDu : ∀ k < 8, blockAt u.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
      blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) ^^^
        ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀)) := by
    intro k hk
    have hks' := hks k hk
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < aregs.length from hk), Option.getD_some] at hks'
    rw [hdata k hk]
    refine congrArg₂ (fun a b : Block => a ^^^ b) ?_ hks'
    exact VG.Proof.Aes.X86_64.AesNi.blockAt_frame ht.frame (by
      intro r hr'; simp only [List.mem_singleton] at hr'; subst r
      exact (hsep.sub_left (by
        simpa only [batchR, ← Offset.add_add, Nat.mul_add] using
          (Offset.sub (s.gpr .rdx) (d := 16 * (j + k)) (e := 16 * j)
            (n := 16) (k := 128) (by omega) (by omega)))).sub_right (work_sub_p s₀))
  have hFu : Frame [batchR s j, workR s₀] s.mem u.mem :=
    (ht.frame.mono (by simp)).trans (hm.mono (by simp [batchR, aregs]))
  refine WP.mono (bump_ok u) fun v ⟨hv8, hvg, hvm, hvl, hvrd, hvwr⟩ => ?_
  refine ⟨hEu.move (fun r _ _ h8 _ => hvg r h8) hvm hvrd hvwr,
    hvm ▸ hTu, hvm ▸ hBu, ?_, ?_, hvm ▸ hFu, ?_, ?_⟩
  · rw [hvl, hlanes .xmm2 (by decide) 0 (by decide)]; exact ht.hash
  · rw [hvm]; exact hDu
  · intro r hrax hr8; rw [hvg r hr8, hg]; exact ht.regs r hrax
  · rw [hv8, hg, ht.regs .r8 (by decide), hv, BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 32 (c + 8) + BitVec.ofNat 32 8 = BitVec.ofNat 32 (c + 16)
    rw [← BitVec.ofNat_add]

end VG.Proof.Gcm.X86_64.StitchAvx8
