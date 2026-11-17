module

public import VerifiedGarbage.Proof.AesGcmSiv.Scratch
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.TopCT
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Seal
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Fn
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs

/-! ### `AesGcmSiv.PPC64LE.Open`, which only this module used -/

section

/-!
# AES-GCM-SIV on PPC64LE: `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `open` is `entry`, the
received tag copied to `W` (`recv`), the keys, counter mode on the data from
it, POLYVAL of the result and the tag input, its tag at `W + 240`, the
comparison, the mask and `restore` (`open_wp`), computing `decryptWith`
(RFC 8452 §5) of the arguments, without a branch on the comparison.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Spec.Aes (bytesAt)
open VG.PPC64LE.Spill (Saved)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesCcm.PPC64LE (wp_mv)

theorem decrypt_eq (hti : TagInputEq) (ciph : Spec.GcmSiv.Cipher) (kl : Nat) (nonce ct aad tag : List Byte) :
    Spec.GcmSiv.decryptWith ciph kl nonce ct aad tag =
      let dk := Spec.GcmSiv.deriveKeys ciph kl nonce
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 nonce
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct) aad) = tag then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct)
      else none := by
  unfold Spec.GcmSiv.decryptWith
  generalize Spec.GcmSiv.deriveKeys ciph kl nonce = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

/-- A buffer missing `W` and the data misses what counter mode writes. -/
theorem buf_cryR {c : Cx} {P : Addr} {len : Nat} (hw : (⟨P, len⟩ : Region).Disjoint ⟨c.W, 3824⟩)
    (hd : (⟨P, len⟩ : Region).Disjoint ⟨c.D, c.n⟩) : ∀ r ∈ cryR c.W c.D c.n, (⟨P, len⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hd

/-- `vg_aes_gcm_siv_open`, for its arguments. -/
theorem open_wp' [VG.Proof.Gcm.PPC64LE.GhashLaw] (hti : TagInputEq) {c : Cx} {s : State} (Ar : Args c s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧
      openOut (Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem c.K c.R) (Spec.GcmSiv.keyLen c.R)
        (bytesAt s.mem c.N 12) (bytesAt s.mem c.D c.n) (bytesAt s.mem c.A c.al) (bytesAt s.mem c.T 16))
        (s'.gpr .r3) (bytesAt s'.mem c.D c.n) c.n := by
  have L := Ar.lay
  have hRb := L.rb
  have hn := L.n_lt
  have hal := L.al_lt
  unfold «open»
  refine WP.seq (WP.mono (entry_wp Ar) fun s₁ En => ?_)
  -- The received tag, copied to `W`.
  refine WP.seq (WP.mono (recv_wp En.env) fun s₂ ⟨pk₂, hm₂⟩ => ?_)
  obtain E₂ := En.env.of_pk pk₂
  obtain fR : Frame [⟨c.W + BitVec.ofNat 64 0, 16⟩] s₁.mem s₂.mem := by
    rw [hm₂, BitVec.add_zero]; exact copy2Mem_frame _ _ _
  have fR' : Frame (wRs c.W [(0, 16)]) s₁.mem s₂.mem := fR
  -- The keys.
  refine WP.seq (WP.mono (keys_wp L E₂) fun s₃ Ky => ?_)
  obtain E₃ := E₂.of_pk Ky.pk
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_wp L E₃) fun s₄ Cr => ?_)
  obtain E₄ := E₃.of_pk Cr.pk
  have fK := Ky.frame
  rw [keyR_eq] at fK
  obtain dC : ∀ {d : Nat}, d + 16 ≤ 96 → ∀ r ∈ cryR c.W c.D c.n, (⟨c.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r :=
    fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inl hd) (by omega_using [hd]) (by decide)
      · exact L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
      · exact L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
      · exact L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
      · exact (L.d_w' (by omega_using [hd])).symm
  obtain a₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 16) 16 = bytesAt s₃.mem (c.W + BitVec.ofNat 64 16) 16 :=
    bytesAt_keep Cr.frame (dC (by decide)) (by decide)
  obtain hG₄ : Spec.Gcm.blockAt s₄.mem (c.W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₄.mem (c.W + BitVec.ofNat 64 16) 16)) := by
    rw [blockAt_frame Cr.frame (dC (by decide)), Ky.hkey, a₄]
  obtain hY₄ : Spec.Gcm.blockAt s₄.mem (c.W + BitVec.ofNat 64 80) = 0 := by
    rw [blockAt_frame Cr.frame (dC (by decide)), Ky.acc]
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (polyval_wp L E₄ hG₄ hY₄) fun s₅ Po => ?_)
  obtain E₅ := E₄.of_pk Po.pk
  -- Its tag at `W + 240`.
  refine WP.seq (WP.mono (tag_wp L E₅ (o := 240) (by decide)) fun s₆ Tg => ?_)
  obtain E₆ := E₅.of_pk Tg.pk
  -- The comparison.
  refine WP.seq (WP.mono (cmp_wp E₆) fun s₇ ⟨pk₇, hm₇, r25₇⟩ => ?_)
  obtain E₇ := E₆.of_pk pk₇
  -- The mask.
  refine WP.seq (WP.mono (mask_wp L E₇ r25₇) fun s₈ ⟨pk₈, r25₈, hm₈⟩ => ?_)
  obtain E₈ := E₇.of_pk pk₈
  have fP := Po.frame
  have fT := Tg.frame
  rw [polyR_eq] at fP
  rw [tagR_eq] at fT
  obtain fM : Frame [⟨c.D, c.n⟩] s₇.mem s₈.mem := by
    rw [hm₈]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [List.length_map, Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)
  obtain f₈ : Frame (mutR c) s₁.mem s₈.mem :=
    (((((fR'.sub (wRs_mut (by decide))).trans (fK.sub (wRs_mut (by decide)))).trans
      (Cr.frame.sub (cryR_mut c))).trans (fP.sub (wRs_mut (by decide)))).trans
      (hm₇ ▸ fT.sub (wRs_mut (by decide)))).trans (fM.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_data)
  obtain pk₁₈ : PK s₁ s₈ := pk₂.trans (Ky.pk.trans (Cr.pk.trans (Po.pk.trans (Tg.pk.trans (pk₇.trans pk₈)))))
  -- The result, and `restore`.
  refine WP.block_append (wp_mv fun s₉ u₉ => WP.block_nil ?_)
  obtain sv₉ : Saved c.W (saveG s) savedL s₉.mem := by rw [u₉.mem]; exact saved_mut L f₈ En.saved
  obtain pk₁₉ : PK s₁ s₉ := pk₁₈.trans (PK.ofUpd u₉)
  refine WP.mono (exit_wp (E₈.of_pk (PK.ofUpd u₉)) sv₉ (by rw [pk₁₉.sp, En.sp])
    (fun r hr => by rw [pk₁₉.gpr r (other_keep r hr), En.others r hr])) fun s' ⟨abi, hm, hr3⟩ => ⟨abi, ?_⟩
  -- What the pieces read.
  obtain hK₁ : Spec.GcmSiv.ctxCiph s₂.mem c.K c.R = Spec.GcmSiv.ctxCiph s.mem c.K c.R := by
    rw [ciph_keep fR' (buf_keep L.k_w (by decide)) hRb]
    unfold Spec.GcmSiv.ctxCiph
    rw [entry_buf En.frame (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])]
  obtain n₂ : bytesAt s₂.mem c.N 12 = bytesAt s.mem c.N 12 := by
    rw [bytesAt_keep fR' (buf_keep L.n_w (by decide)) (by decide), entry_buf En.frame L.n_w (by decide)]
  obtain n₄ : bytesAt s₄.mem c.N 12 = bytesAt s.mem c.N 12 := by
    rw [bytesAt_keep Cr.frame (buf_cryR L.n_w L.n_d) (by decide),
      bytesAt_keep fK (buf_keep L.n_w (by decide)) (by decide), n₂]
  obtain a₄' : bytesAt s₄.mem c.A c.al = bytesAt s.mem c.A c.al := by
    rw [bytesAt_keep Cr.frame (buf_cryR L.a_w L.a_d) (by omega_using [hal]),
      bytesAt_keep fK (buf_keep L.a_w (by decide)) (by omega_using [hal]),
      bytesAt_keep fR' (buf_keep L.a_w (by decide)) (by omega_using [hal]), entry_buf En.frame L.a_w (by omega_using [hal])]
  obtain d₃ : bytesAt s₃.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [bytesAt_keep fK (buf_keep L.d_w (by decide)) (by omega_using [hn]),
      bytesAt_keep fR' (buf_keep L.d_w (by decide)) (by omega_using [hn]), entry_buf En.frame L.d_w (by omega_using [hn])]
  obtain tag₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 0) 16 = bytesAt s.mem c.T 16 := by
    rw [bytesAt_keep fK (w_keep L (by decide) (by decide)) (by decide), BitVec.add_zero, hm₂, copy2Mem_bytes,
      entry_buf En.frame L.t_w (by decide)]
  obtain tag₆ : bytesAt s₆.mem (c.W + BitVec.ofNat 64 0) 16 = bytesAt s.mem c.T 16 := by
    rw [bytesAt_keep fT (w_keep L (by decide) (by decide)) (by decide),
      bytesAt_keep fP (w_keep L (by decide) (by decide)) (by decide),
      bytesAt_keep Cr.frame (dC (by decide)) (by decide), tag₃]
  rw [BitVec.add_zero] at tag₃ tag₆
  obtain ci₅ : Spec.GcmSiv.ctxCiph s₅.mem (c.W + BitVec.ofNat 64 256) c.R =
      Spec.GcmSiv.ctxCiph s₃.mem (c.W + BitVec.ofNat 64 256) c.R := by
    rw [ciph_keep fP (w_keep L (by decide) (by decide)) hRb, ciph_cryR L Cr.frame]
  obtain d₇ : bytesAt s₇.mem c.D c.n = bytesAt s₄.mem c.D c.n := by
    rw [hm₇, bytesAt_keep fT (buf_keep L.d_w (by decide)) (by omega_using [hn]),
      bytesAt_keep fP (buf_keep L.d_w (by decide)) (by omega_using [hn])]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₂] at au ci
  have pt₄ := Cr.data
  rw [tag₃, d₃, ci] at pt₄
  have po := Po.out
  rw [a₄, ← au, n₄, a₄', pt₄] at po
  have tg := Tg.out
  rw [ci₅, ci, po] at tg
  obtain r3' : s'.gpr .r3 = s₇.gpr .r25 := by rw [hr3, u₉.gpr, r25₈]
  rw [r25₇, tag₆, tg] at r3'
  obtain md : bytesAt s'.mem c.D c.n = (bytesAt s₇.mem c.D c.n).map fun b =>
      if bytesAt s.mem c.T 16 = Spec.GcmSiv.ctxCiph s₅.mem (c.W + BitVec.ofNat 64 256) c.R
        (bytesAt s₅.mem (c.W + BitVec.ofNat 64 96) 16) then b else 0 := by
    obtain e := Proof.AesGcm.PPC64LE.bytesAt_writeBytes_self s₇.mem c.D
      ((bytesAt s₇.mem c.D c.n).map fun b => if bytesAt s₆.mem c.W 16 =
        bytesAt s₆.mem (c.W + BitVec.ofNat 64 240) 16 then b else 0)
      (by rw [List.length_map, Proof.Cmac.bytesAt_length]; omega_using [hn])
    rw [List.length_map, Proof.Cmac.bytesAt_length] at e
    rw [hm, u₉.mem, hm₈, e, tag₆, Tg.out]
  rw [d₇, pt₄, ci₅, ci, po] at md
  rw [decrypt_eq hti]
  simp only
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem c.K c.R) (Spec.GcmSiv.keyLen c.R)
    (bytesAt s.mem c.N 12) = dk at md r3'
  obtain hlen : (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem c.T 16))
      (bytesAt s.mem c.D c.n)).length = c.n := by
    rw [GcmSiv.length_ctr (Spec.GcmSiv.aes dk.2) (fun y => GcmSiv.aesWith_length _ _ y), Proof.Cmac.bytesAt_length]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem c.N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem c.T 16))
        (bytesAt s.mem c.D c.n)) (bytesAt s.mem c.A c.al)) = bytesAt s.mem c.T 16
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    have hc' := hc.symm
    unfold openOut
    refine ⟨?_, ?_⟩
    · rw [r3', ite_eq_left_of_eq_true _ _ (eq_true hc')]; rfl
    · rw [md]; simp only [ite_eq_left_of_eq_true _ _ (eq_true hc'), List.map_id']
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    obtain hc' : ¬bytesAt s.mem c.T 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem c.N 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem c.T 16))
          (bytesAt s.mem c.D c.n)) (bytesAt s.mem c.A c.al)) := fun h => hc h.symm
    unfold openOut
    refine ⟨?_, ?_⟩
    · rw [r3', ite_eq_right_of_eq_false _ _ (eq_false hc')]; rfl
    · rw [md]; simp only [ite_eq_right_of_eq_false _ _ (eq_false hc'), List.map_const', hlen, Spec.GcmSiv.zeros]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] (hti : TagInputEq) {s : State} (h : openPPC64LE.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openPPC64LE.post s s' := by
  obtain A := args_of_open h
  refine WP.mono (open_wp' hti A) fun s' ⟨ga, hp⟩ => ⟨ga, ?_⟩
  simp only [openPPC64LE]
  simpa only [cxOf] using hp

end VG.Proof.AesGcmSiv.PPC64LE

end

end


/-!
# AES-GCM-SIV on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, given that the tag input computed with GHASH is the RFC's
(`TagInputEq`, which the registration file binds to
`Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`, so that only that leaf
imports its algebra), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean` with
the working space as a last argument (`Proof/AesGcmSiv/Scratch.lean`, 478
doublewords), with no stack: a call (`bl`) stores nothing in memory, and
each function saves the return address in the working space. Then the code
in a frame that allocates the working space (`Verified.stackScratchArgs`):
it is the first stack argument, so the frame of 3936 bytes holds the
frame's own header and Parameter Save Area, the address of the working
space and the working space.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcmSiv.PPC64LE

/-! ## Correctness and constant time -/

theorem seal_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (hti : TagInputEq) (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  seal_wp hti hs

theorem open_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (hti : TagInputEq) (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openPPC64LE.post s s' :=
  open_wp hti hs

/-- A state satisfying the precondition of `vg_aes_gcm_siv_seal`: no
additional data, no data, the tag at `0x4800` and `work` at `0x5000`, its
address at `sp + 96`. -/
def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x3000 | .r8 => 0x4000 | .r10 => 0x4800 | _ => 0
  lr := 0
  sp := 0x8000
  mem a := bif Nat.beq a.toNat 0x8061 then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x8060, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x4800, 16⟩, ⟨0x5000, 3824⟩]

/-- A state satisfying the precondition of `vg_aes_gcm_siv_open`: as
`sealSat`, with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4800, 16⟩, ⟨0x8060, 8⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 3824⟩] }

/-! ## The shared contracts -/

theorem seal_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] (hti : TagInputEq) :
    Verified PPC64LE.target «seal» (Proof.AesGcmSiv.sealScratchContract PPC64LE.abi 478) :=
  Verified.of_correct (seal_correct hti) seal_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
            Proof.AesGcmSiv.sealRoundsPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi,
            PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
            Proof.AesGcmSiv.sealRoundsPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi,
            PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
          sig_and_intros
          sig_close
          all_goals first
            | with_reducible assumption
            | sig_disjoint_symm
            | omega
            | bv_omega
        post := by
          sig_implies_post [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig,
            Spec.GcmSiv.sealPre, Proof.AesGcmSiv.sealRoundsPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds,
            PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
        pub := by
          sig_implies_pub [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig,
            Spec.GcmSiv.sealPre, Proof.AesGcmSiv.sealRoundsPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds,
            PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig,
            Spec.GcmSiv.sealPre, Proof.AesGcmSiv.sealRoundsPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds,
            PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
            [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat }

theorem open_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] (hti : TagInputEq) :
    Verified PPC64LE.target «open» (Proof.AesGcmSiv.openScratchContract PPC64LE.abi 478) :=
  Verified.of_correct (open_correct hti) open_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
            Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openOut,
            args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD,
            List.range, List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
            Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openOut,
            args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD,
            List.range, List.range.loop]
          sig_and_intros
          sig_close
          all_goals first
            | with_reducible assumption
            | sig_disjoint_symm
            | omega
            | bv_omega
        -- `h` and the goal match on the same outcome of `decryptWith` with
        -- different matchers (`openOut`'s and `openContract`'s): split on it
        -- rather than have `exact h` unfold both to unify them.
        post := by
          intro s s' _ h
          sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
            Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes,
            args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD,
            List.range, List.range.loop]
          sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
            Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes,
            args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD,
            List.range, List.range.loop] at h
          intro _
          unfold openOut at h
          split at h <;> rename_i heq <;> rw [heq] <;> exact h
        pub := by
          sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
            Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay,
            onePub, openRes, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg,
            PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
            Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay,
            onePub, openRes, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg,
            PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
            [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

/-! ## The working space on the stack -/

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space: no stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩], wr := [⟨0x4000, 0⟩, ⟨0x4800, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesGcmSiv.sealRoundsContract PPC64LE.abi 3936).pre s := by
  implies_sat [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Proof.AesGcmSiv.sealRoundsPost,
    PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] (hti : TagInputEq) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 3936 0 «seal»)
      (Proof.AesGcmSiv.sealRoundsContract PPC64LE.abi 3936) :=
  Verified.stackScratchArgsKept (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 478) (pre := Spec.GcmSiv.sealPre PPC64LE.abi.ptrBits)
    (post := Proof.AesGcmSiv.sealRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3936) (m := 0)
    (seal_verified hti) (by decide) (by decide) (Proof.AesGcmSiv.sealPre_local _) (Proof.AesGcmSiv.sealPost_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space: no stack arguments. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4800, 16⟩], wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesGcmSiv.openRoundsContract PPC64LE.abi 3936).pre s := by
  implies_sat [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost,
    Spec.GcmSiv.openLeak, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] (hti : TagInputEq) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 3936 0 «open»)
      (Proof.AesGcmSiv.openRoundsContract PPC64LE.abi 3936) :=
  Verified.stackScratchArgsKept (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 478) (pre := Spec.GcmSiv.openPre PPC64LE.abi.ptrBits)
    (post := Proof.AesGcmSiv.openRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3936) (m := 0)
    (leak := some (Spec.GcmSiv.openLeak PPC64LE.abi.ptrBits))
    (Proof.AesGcmSiv.Verified.of_openScratch (open_verified hti)) (by decide) (by decide)
    (Proof.AesGcmSiv.openPre_local _) (Proof.AesGcmSiv.openPost_local _)
    openFrameSat_pre (hleak := Proof.AesGcmSiv.openLeak_local _)

end VG.Proof.AesGcmSiv.PPC64LE
