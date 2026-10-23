module

public import VerifiedGarbage.Impl.AesCfb.AArch64.Decrypt
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # CFB's ciphertext reload, XOR, and plaintext stores -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.Impl.AesCfb.AArch64.Decrypt

theorem finish_ok (b : VReg) (j : Nat) (s : State) (hb : b ≠ .v31) (hj : j < 4096)
    (hin : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (.block (finish b j)) s fun t =>
      t.mem = s.mem.write (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 16
        (s.v b ^^^ s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 128) ∧
      t.v .v31 = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 128 ∧
      t.gpr = s.gpr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .v31 → t.v r = s.v r) := by
  rw [finish, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega) (inRegions_wr hin), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_strq (by omega) hin, WP.block_nil ?_⟩
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, fun r h1 h2 => by simp [State.setV, h1, h2]⟩
  · simp [State.setV, hb]
  · simp [State.setV, hb, Ne.symm hb]

/-- The unprocessed blocks still contain their original 128-bit ciphertext. -/
theorem original_word {m₀ m : Mem} {D : Addr} {n k j : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) (hj : k ≤ j) (hjn : j < n) :
    m.readW (D + BitVec.ofNat 64 (16*j)) 128 =
      m₀.readW (D + BitVec.ofNat 64 (16*j)) 128 := by
  apply ext_vbyte
  intro i hi
  have he := congrArg (fun v : Spec.Aes.State => v[i]) (ecbInv_orig h hj hjn)
  simpa only [vbyte_readW _ _ hi, Spec.Aes.stateAt, Vector.getElem_ofFn] using he

/-- Store a group, keeping each ciphertext until the following block uses it. -/
theorem finishData_ok {m₀ : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State}
    {chain : Nat → BitVec 128} (hn : 16*n ≤ 2^64)
    (hnext : ∀ k < n, chain (k+1) = m₀.readW (D + BitVec.ofNat 64 (16*k)) 128) :
    ∀ (regs : List VReg) (j : Nat) (s : State), regs.Nodup → .v31 ∉ regs → .v16 ∉ regs →
    s.gpr .x2 = D + BitVec.ofNat 64 (16*c) → j + regs.length ≤ 4096 → c+j+regs.length ≤ n →
    (⟨D,16*n⟩ : Region) ∈ s.wr → EcbInv m₀ s.mem D n (c+j) F →
    s.v .v31 = chain (c+j) →
    (∀ k (h : k < regs.length), ∀ i < 16,
      vbyte (s.v regs[k]) i ^^^ vbyte (m₀.readW (D + BitVec.ofNat 64 (16*(c+j+k))) 128) i =
        (F (c+j+k)).getD i 0) →
    WP isa (.block (finishData regs j)) s fun t =>
      EcbInv m₀ t.mem D n (c+j+regs.length) F ∧
      t.v .v31 = chain (c+j+regs.length) ∧ Frame [⟨D,16*n⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .v31 → r ∉ regs → t.v r = s.v r)
  | [], _, s, _, _, _, _, _, _, _, hD, hC, _ =>
    WP.block_nil ⟨hD,hC,Frame.refl _ _,rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩
  | b :: bs, j, s, hnd, h31, h16, hx, hj, hc, hw, hD, hC, hF => by
    have hb31 : b ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h31' : .v31 ∉ bs := fun h => h31 (List.mem_cons_of_mem _ h)
    have h16' : .v16 ∉ bs := fun h => h16 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hj hc
    have ha : s.gpr .x2 + BitVec.ofNat 64 (16*j) = D + BitVec.ofNat 64 (16*(c+j)) := by
      rw [hx, Offset.add_add_eq D (show 16*c+16*j=16*(c+j) by omega)]
    rw [finishData, WP.block_append_iff]
    refine WP.mono (finish_ok b j s hb31 (by omega) (by
      rw [ha]; exact ⟨_, hw, Offset.contains_base D (by omega) (by omega)⟩))
      fun t ⟨hm,hv,hg,hsp,hrd,hwr,ho⟩ => ?_
    rw [ha] at hm hv
    have hB : ∀ i < 16, vbyte (s.v b ^^^ s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16*j)) 128) i = (F (c+j)).getD i 0 := by
      intro i hi
      have hz := hF 0 (by simp) i hi
      simpa only [ha, vbyte_xor, original_word hD (Nat.le_refl _) (by omega), Nat.add_zero, List.getElem_cons_zero] using hz
    have hs := Aese.ecbInv_write hn (by omega) hD hB
    rw [ha] at hs
    rw [← hm] at hs
    have hC' : t.v .v31 = chain (c+(j+1)) := by
      rw [hv, original_word hD (Nat.le_refl _) (by omega),
        ← hnext (c+j) (by omega), show c+j+1=c+(j+1) by omega]
    refine WP.mono (finishData_ok (m₀ := m₀) (D := D) (n := n) (c := c) (F := F) (chain := chain) hn hnext bs (j+1) t (List.nodup_cons.mp hnd).2 h31' h16'
      (hg ▸ hx) (by omega) (by omega) (hwr ▸ hw)
      (by rw [show c+(j+1)=c+j+1 by omega]; exact hs.1) hC' (fun k hk i hi => by
        rw [ho _ (fun h => hbs (h ▸ List.getElem_mem hk)) (fun h => h31' (h ▸ List.getElem_mem hk)), show c+(j+1)+k=c+j+(k+1) by omega]
        exact hF (k+1) (by simp; omega) i hi))
      fun u ⟨hu,hv',hf',hg',hsp',hrd',hwr',ho'⟩ => ?_
    have he : c+(j+1)+bs.length = c+j+(b::bs).length := by simp; omega
    rw [he] at hu hv'
    exact ⟨hu,hv',hs.2.trans hf',hg'.trans hg,hsp'.trans hsp,hrd'.trans hrd,hwr'.trans hwr,
      fun r hr hrs => (ho' r hr (fun h => hrs (List.mem_cons_of_mem _ h))).trans
        (ho r (fun h => hrs (h ▸ List.mem_cons_self)) hr)⟩

end VG.Proof.AesCfb.AArch64.Decrypt
