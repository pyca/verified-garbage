module

public import VerifiedGarbage.Proof.MillerRabin.X86.WindowFlag
public import VerifiedGarbage.Proof.MillerRabin.X86.WindowAdvance

/-! # The final header updates of an exponent window -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem window_end {σ s : State} {base : Addr} {bytes w d k : Nat} {F E1 E2 : Bool}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes) (hd : d < 16) (hk : 0 < k ∧ k < 2 ^ 32)
    (digit : s.mem.readW (off base sV) 32 >>> 28 = BitVec.ofNat 32 d)
    (count : s.mem.readW (off base sK) 32 = BitVec.ofNat 32 k)
    (flag : s.mem.readW (off base sF) 32 = BitVec.ofNat 32 F.toNat)
    (equal1 : s.mem.readW (off base sE1) 32 = BitVec.ofNat 32 E1.toNat)
    (equal2 : s.mem.readW (off base sE2) 32 = BitVec.ofNat 32 E2.toNat) :
    WP isa (.block winEnd) s fun t => Stage base bytes w σ t ∧
      w32 t.mem base sF = (if d = 0 then F else E1 || E2).toNat ∧
      w32 t.mem base sV = (s.mem.readW (off base sV) 32 <<< 4).toNat ∧
      w32 t.mem base sK = k - 1 ∧ t.zf = some (decide ((k - 1) % 8 = 0)) ∧
      Frame ([sF, sV, sK].map (fun a => ⟨off base a, 4⟩)) s.mem t.mem := by
  rw [winEnd, WP.block_append_iff]
  refine WP.mono (window_flag h hf hd digit flag equal1 equal2) ?_
  rintro u ⟨hu, flagU, wordU, frameU⟩
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) hf
  have countU : u.mem.readW (off base sK) 32 = BitVec.ofNat 32 k :=
    (workspace_frame_word h.context.ws.nowrap (Nat.le_trans (by decide : sK + 4 ≤ 256) hdrFit)
      (Nat.le_trans (by decide : sF + 4 ≤ 256) hdrFit) (by decide) frameU).trans count
  refine WP.mono (window_advance hu hf hk wordU countU) ?_
  rintro t ⟨ht, valueT, countT, zeroT, frameT⟩
  have sameF := headers_frame_word (ds := [sV, sK]) hu.context.ws.nowrap
    (Nat.le_trans (by decide : sF + 4 ≤ 256) hdrFit)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> exact Nat.le_trans (by decide) hdrFit)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> decide) frameT
  refine ⟨ht, (congrArg BitVec.toNat sameF).trans flagU, valueT, countT, zeroT, ?_⟩
  have f : Frame ([sF, sV, sK].map (fun a => ⟨off base a, 4⟩)) s.mem u.mem := frameU.mono (by
    intro r hr; rw [List.mem_singleton.mp hr]; simp)
  exact f.trans (frameT.mono (by
    intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    tauto))

end VG.Proof.MillerRabin.X86
