module

import VerifiedGarbage.Proof.AesCcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Cmp
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import Mathlib.Data.List.Induction
public import VerifiedGarbage.Impl.AesCcm.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesCcm.Ctr
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Entry
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Spec.Cmac
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Chunk
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Ctrs
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Exit
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Mac
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp

/-!
# AES-CCM on PPC64LE: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is `entry`, `Ctr₀`
(`ctrs`), counter mode over the data (`ctr`), which decrypts it, the MAC of
the plaintext (`mac uO`), encrypted at `W + 96` (`tag uO`), the comparison
with the received tag, whose address the entry keeps in `W` (`cmp`), the
plaintext zeroed unless they are equal (`mask`), the result in `r3` and
`restore` (`open_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_ld
open VG.Spec.Aes (bytesAt)
open VG.PPC64LE.Spill (Saved)
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_ld)
open VG.Proof.AesCcm (xorFrom length_bytesAt crypt_eq take_xorFrom_zero mac_eq length_xorFrom BlockCipher
  cryptTag_eq_iff)

theorem cmpR_mut (c : Cx) : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_hi (by decide) (by decide)

theorem maskR_mut (c : Cx) : ∀ r ∈ [(⟨c.D, c.n⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_data

theorem cmpR_list (W : Addr) : [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)] =
    [(256, 32)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

theorem length_chain {ciph : Spec.Ccm.Cipher} (hc : BlockCipher ciph) :
    ∀ (ms : List (List Byte)) (c : List Byte), c.length = 16 → (Spec.Cmac.chain ciph c ms).length = 16
  | [], _, h => h
  | _ :: ms, _, _ => length_chain hc ms _ (hc _)

/-- The data masked: itself if `P`, zeros if not. -/
theorem masked {m : Mem} {D : Addr} {n : Nat} (hn : n < 2 ^ 64) (P : Prop) [Decidable P] :
    bytesAt (writeBytes m D ((bytesAt m D n).map fun b => if P then b else 0)) D n =
      if P then bytesAt m D n else Spec.Ccm.zeros n := by
  rw [Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [List.length_map, length_bytesAt]) hn,
    List.length_map, length_bytesAt, List.drop_eq_nil_of_le (by rw [length_bytesAt]), List.append_nil]
  by_cases hP : P
  · simp [hP]
  · simp only [hP, ite_false, Spec.Ccm.zeros]
    rw [List.map_const', length_bytesAt]

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧
      openOut (Spec.Ccm.decryptWith (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
          (bytesAt s.mem c.D c.n) (bytesAt s.mem c.A c.al) (bytesAt s.mem c.T c.tl)) (s'.gpr .r3)
        (bytesAt s'.mem c.D c.n) c.n := by
  have L := Ar.lay
  have ht16 := L.t16
  have hn := L.n_lt
  unfold «open»
  refine WP.seq (WP.mono (entry_wp Ar) fun s₁ En => ?_)
  have hN₁ : Buf c s₁ N c.nl := Ar.nonce.of_eq En.rd En.wr
  refine WP.seq (WP.mono (ctrs_wp L En.env hN₁ En.r5 En.r6) fun s₂ ⟨pk₂, f₂, c₂⟩ => ?_)
  rw [entry_buf En.frame Ar.nonce] at c₂
  have hnl : (bytesAt s.mem N c.nl).length = c.nl := length_bytesAt _ _ _
  have f₂' : Frame (mutR c) s₁.mem s₂.mem := f₂.sub (c0_mut c)
  have E₂ := En.env.of_pk pk₂
  refine WP.seq (WP.mono (ctr_wp L E₂ hnl c₂) fun s₃ ⟨pk₃, f₃, h₃⟩ => ?_)
  have E₃ := E₂.of_pk pk₃
  have f₁₃ : Frame (mutR c) s₁.mem s₃.mem := f₂'.trans (f₃.sub (crR_mut c))
  have c₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.Cmac.bytesAt_frame f₃ (crR_disj L (.inl (by decide))) (by decide), c₂]
  refine WP.seq (WP.mono (mac_wp L E₃ (En.slots.mut L f₁₃) hnl c₃ (.inr rfl)) fun s₄ M => ?_)
  have fM := M.frame
  rw [macR_list] at fM
  have c₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.Cmac.bytesAt_frame fM (w_keep L (by decide) (by decide)) (by decide), c₃]
  have E₄ := E₃.of_pk M.pk
  refine WP.seq (WP.mono (tag_wp L E₄ hnl c₄ (.inr rfl)) fun s₅ ⟨pk₅, _, f₅, h₅⟩ => ?_)
  have E₅ := E₄.of_pk pk₅
  have f₁₄ : Frame (mutR c) s₁.mem s₄.mem := f₁₃.trans (M.frame.sub (macR_mut (.inr rfl)))
  have f₁₅ : Frame (mutR c) s₁.mem s₅.mem := f₁₄.trans (f₅.sub (ctrR_mut c (.inr rfl)))
  -- The address of the received tag, from its slot.
  refine WP.seq (wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by decide) (by rw [E₅.r14]; rfl)
    (E₅.perm.wR (by decide)) fun s₆ u₆ => WP.block_nil ?_)
  have pk₆ : PK s₅ s₆ := PK.ofUpd u₆
  have m₆ : s₆.mem = s₅.mem := u₆.mem
  have r18₆ : s₆.gpr .r18 = c.T := by rw [u₆.gpr]; exact (En.slots.mut L f₁₅).tag
  refine WP.seq (WP.mono (cmp_wp L (E₅.of_pk pk₆) r18₆) fun s₇ ⟨pk₇, f₇, r21₇⟩ => ?_)
  rw [m₆] at r21₇ f₇
  -- What the comparison compares.
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m c.K c.R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have k₁ := entry_ciph L En.frame
  have k₂ : Spec.Ccm.ctxCiph s₂.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₂', k₁]
  have k₃ : Spec.Ccm.ctxCiph s₃.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₃, k₁]
  have k₄ : Spec.Ccm.ctxCiph s₄.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₄, k₁]
  have bD := L.bufD Ar.perm
  have bD₁ : Buf c s₁ c.D c.n := bD.of_eq En.rd En.wr
  have hd₂ : bytesAt s₂.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [c0_list] at f₂
    rw [Proof.Cmac.bytesAt_frame f₂ (bufW_keep bD₁ (by decide)) (by omega), entry_buf En.frame bD]
  have ha₃ : bytesAt s₃.mem c.A c.al = bytesAt s.mem c.A c.al := by
    rw [aad_mut L f₁₃, entry_buf En.frame (L.bufA Ar.perm)]
  have hpt : bytesAt s₃.mem c.D c.n =
      Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n) := by
    rw [h₃, k₂, hd₂, crypt_eq (hBC _)]
  have hd₇ : bytesAt s₇.mem c.D c.n = bytesAt s₃.mem c.D c.n := by
    rw [cmpR_list] at f₇
    rw [ctrR_list] at f₅
    rw [Proof.Cmac.bytesAt_frame f₇ (bufW_keep bD₁ (by decide)) (by omega),
      Proof.Cmac.bytesAt_frame f₅ (bufW_keep bD₁ (by decide)) (by omega),
      Proof.Cmac.bytesAt_frame fM (bufW_keep bD₁ (by decide)) (by omega)]
  have hrecv : bytesAt s₅.mem c.T c.tl = bytesAt s.mem c.T c.tl := by
    rw [tag_mut L f₁₅, Proof.Cmac.bytesAt_frame En.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_w.sub_right (Lay.wSub (by decide))) (by omega)]
  have hcomp : bytesAt s₅.mem (c.W + BitVec.ofNat 64 96) c.tl =
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))) := by
    rw [show c.W + BitVec.ofNat 64 96 = c.W + BitVec.ofNat 64 uO from rfl, Proof.AesCcm.bytesAt_prefix s₅.mem _ L.t16,
      h₅, k₄, take_xorFrom_zero (hBC _) _ (length_bytesAt _ _ _) L.t16, M.out, k₃,
      ha₃, hpt, mac_eq _ _ (by rw [hnl]; have := L.h13; omega)]
    rfl
  rw [hcomp, hrecv] at r21₇
  refine WP.seq (WP.mono (mask_wp L (E₅.of_pk (pk₆.trans pk₇)) r21₇) fun s₈ ⟨pk₈, r21₈, m₈⟩ => ?_)
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₉ u₉ => ?_
  have f₈ : Frame [⟨c.D, c.n⟩] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_frame _ _ _ (by rw [List.length_map, length_bytesAt]; exact Region.contains_self _ _)
  have f₁₈ : Frame (mutR c) s₁.mem s₈.mem :=
    (f₁₅.trans ((m₆ ▸ (show Frame [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)] s₆.mem s₇.mem by
      rw [m₆]; exact f₇)).sub (cmpR_mut c))).trans (f₈.sub (maskR_mut c))
  have pk₁₉ : PK s₁ s₉ := pk₂.trans (pk₃.trans (M.pk.trans (pk₅.trans (pk₆.trans (pk₇.trans (pk₈.trans
    (PK.ofUpd u₉)))))))
  have sv₉ : Saved c.W (saveG s) savedL s₉.mem := by rw [u₉.mem]; exact saved_mut L f₁₈ En.saved
  refine WP.mono (exit_wp (En.env.of_pk pk₁₉) sv₉ (by rw [pk₁₉.sp, En.sp])
    (fun r hr => by rw [pk₁₉.gpr r (other_keep r hr), En.others r hr])) fun s' ⟨abi, hm, r3'⟩ => ⟨abi, ?_⟩
  -- The result.
  have hmlen : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
      (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))).length =
      c.tl := by
    rw [mac_eq _ _ (by rw [hnl]; have := L.h13; omega), List.length_take,
      length_chain (hBC _) _ _ (by simp [Spec.Cmac.zeros])]
    omega
  have hiff := cryptTag_eq_iff (hBC s.mem) L.t16 (bytesAt s.mem N c.nl) hmlen (length_bytesAt s.mem c.T c.tl)
  have hr3 : s'.gpr .r3 = s₇.gpr .r21 := by rw [r3', u₉.gpr, r21₈]
  simp only [openOut, Spec.Ccm.decryptWith]
  rw [hr3, r21₇, hm, u₉.mem, m₈, masked hn, hd₇, hpt]
  by_cases he : Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
      (bytesAt s.mem c.T c.tl) = Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (bytesAt s.mem c.A c.al) (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl)
          (bytesAt s.mem c.D c.n))
  · have hq := hiff.mpr he.symm
    simp only [he, hq, ite_true]
    exact ⟨by decide, trivial⟩
  · have hq : ¬ _ := fun h => he (hiff.mp h).symm
    simp only [he, hq, ite_false]
    exact ⟨by decide, trivial⟩

/-- `vg_aes_ccm_open`. -/
theorem open_wp {s : State} (h : openPPC64LE.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openPPC64LE.post s s' :=
  WP.mono (open_wp' (args_of_open h)) fun _ hp => hp

end VG.Proof.AesCcm.PPC64LE
