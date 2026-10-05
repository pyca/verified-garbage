import VerifiedGarbage.Proof.AesGcm.X86.StreamCrypt
import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcm.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Seal`. -/
section

/-!
# AES-GCM on x86: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. The entry (`oneEntry_pc`),
`J₀` and the additional data (`oneAad_pc`), the data encrypted
(`oneCrypt_pc`), the tag into `W` (`oneTag_pc`) and copied to `tag`
(`tagOut_ok`), and the exit, as one `Pc` (`seal_pc`): correct
(`seal_correct`) and constant time (`seal_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph zeros padLen inc32 ghash ghashFrom blocks toBytes ofBytes gctr
  fullTag encryptWith)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

/-- The padded input of GHASH, as `seal` and `open` absorb it: the
additional data padded, then the data, padded. -/
theorem padded_eq (a c : List Byte) :
    Proof.Gcm.padded a c = a ++ zeros (padLen a.length) ++ c ++
      zeros (padLen (a ++ zeros (padLen a.length) ++ c).length) := by
  by_cases hc : c = []
  · subst hc
    have h0 : padLen (a ++ zeros (padLen a.length)).length = 0 := by
      have := Proof.Gcm.length_pad_mod a.length
      simp only [List.length_append, Proof.Gcm.length_zeros, padLen] at this ⊢; omega
    simp only [Proof.Gcm.padded, Proof.Gcm.ghashInput_nil, List.append_nil, h0]
    simp [zeros]
  · simp only [Proof.Gcm.padded, Proof.Gcm.ghashInput_of_ne hc]

theorem toBytes_take16 (x : Block) : (toBytes x).take 16 = toBytes x :=
  List.take_of_length_le (by rw [Proof.Cmac.toBytes_length])

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

/-- A block of the state before the counter block, apart from what `crypt` writes. -/
theorem st_crFrameO {d : Nat} (hd : d + 16 ≤ 48) :
    ∀ r ∈ crFrame (stOf (p.2 8)) (p.2 8) p.1 28 (p.2 6) (p.2 7).toNat,
      (⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (G.d_w.sub_right (by rw [st_eq G]; exact Lay.wSub (by omega))).symm
  · exact Lay.st_st (.inl (by omega)) (by omega) (by decide)
  · exact G.L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (G.L.stk_st (by omega)).symm

/-- The data, apart from the regions of `W` and the stack the pieces write. -/
theorem d_oF : ∀ r ∈ oF p, (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.k_d.symm

theorem d_woF {o : Nat} (ho : o + 16 ≤ 2560) :
    ∀ r ∈ ⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: oF p, (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact G.d_w.sub_right (Lay.wSub ho)
  · exact VG.Proof.AesGcm.X86.d_oF G r hr

end

theorem seal_eq : («seal» vg.callees) = .seq (oneEntry 9 ([(8, tpO)].flatMap (fun (p : Nat × Nat) => VG.Impl.AesGcm.X86.keep p.1 p.2)))
    (.seq (oneAad vg.callees) (.seq (oneCrypt vg.callees) (.seq (oneTag vg.callees 0)
      (.seq (tagOut 0) (.block restore))))) := rfl

theorem seal_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => sealPre s₀ ∧ pubSw 10 8 s₀ = p ∧ s = s₀) («seal» vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ sealX86.post s₀ s') := by
  by_cases hex : ∃ s₀, sealPre s₀ ∧ pubSw 10 8 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have G : OL p := (op_of_seal hz).ol rfl (by decide) hzp
  have L := G.L
  have a8 : ∀ {s₀ : State}, pubSw 10 8 s₀ = p → arg s₀ 8 = p.2 9 := fun h => pubSw_last h (by decide) rfl
  have a67 : ∀ {s₀ : State}, pubSw 10 8 s₀ = p → arg s₀ 6 = p.2 6 ∧ arg s₀ 7 = p.2 7 := fun h =>
    ⟨pubSw_arg h (by decide) (by decide) (by decide), pubSw_arg h (by decide) (by decide) (by decide)⟩
  obtain ⟨-, fT, tw, rt, dt⟩ := sealPre_tag hz
  rw [a8 hzp] at fT
  rw [a8 hzp, pubSw_W hzp (m := 9) (by decide) rfl] at tw
  rw [a8 hzp, pubSw_esp hzp] at rt
  rw [a8 hzp, (a67 hzp).1, (a67 hzp).2] at dt
  rw [VG.Proof.AesGcm.X86.seal_eq]
  -- The entry, `J₀` and the additional data.
  refine Pc.seq (oneEntry_pc 10 9 rfl (by decide) [(8, tpO)] (by decide) (by decide) (by simp) sealPre
    (fun _ h => op_of_seal h) p G (by taint_decide) (by taint_decide)) ?_
  refine Pc.seq (Pc.lift (oneAad_pc G) (fun s₀ s => (s₀, s)) fun s₀ s h => ⟨h.1, rfl⟩) ?_
  -- The data encrypted.
  refine Pc.seq (Pc.lift (oneCrypt_pc G (fun s₀ => inc32 (jOf p s₀))) (fun s₀ s => (s₀, s))
    fun s₀ s ⟨_, _, ⟨ha, _⟩, _⟩ => ⟨⟨ha.o, Proof.Gcm.ctr_zero _ _ _ _ ha.cb⟩, rfl⟩) ?_
  -- The tag.
  refine Pc.seq (Pc.lift (oneTag_pc G (o := 0) (.inl rfl)) (fun s₀ s => (s₀, s))
    fun s₀ s ⟨s₂, ⟨_, _, ⟨ha, _⟩, _⟩, ⟨o', _, fC⟩, _⟩ => ⟨⟨o', ?_, ?_⟩, rfl⟩) ?_
  · have := blockAt_frame fC (VG.Proof.AesGcm.X86.st_crFrameO G (d := 0) (by decide))
    rw [BitVec.add_zero] at this
    rw [this]; exact ha.j
  · have hl : (xA p s₀).length % 16 = 0 := by
      simp only [xA, List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
    exact ha.y.congr (blockAt_frame fC (VG.Proof.AesGcm.X86.st_crFrameO G (by decide))) (by rw [hl]; rfl)
  -- The tag copied to `tag`.
  refine Pc.seq (Pc.of (I := fun s => WEnv (p.2 8) s ∧ slotv s.mem (p.2 8) tpO = p.2 9 ∧
      Covers [⟨w64 (p.2 9), 16⟩] s.wr)
    (R := fun s s' => bytesAt s'.mem (w64 (p.2 9)) 16 = bytesAt s.mem (w64 (p.2 8) + BitVec.ofNat 64 0) 16 ∧
      Frame [⟨w64 (p.2 9), 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (fun s hs => tagOut_ok hs.1 (by decide) hs.2.1 hs.2.2 fT) (tagOut_ct rfl fun s hs => ⟨hs.1, hs.2.1⟩) _
    (fun s₀ s ⟨_, ⟨_, ⟨_, ⟨_, _, hpub, hpre⟩, _⟩, _⟩, ⟨o₄, _, _⟩, _⟩ => ⟨⟨o₄.env.ebp, o₄.env.wW, L.fw⟩,
      by rw [o₄.tp, a8 hpub], by rw [o₄.wr, ← a8 hpub]; exact (sealPre_tag hpre).1⟩)) ?_
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s'' ⟨s, ⟨s₃, ⟨s₂, ⟨sE, ⟨hE, _, hpub, _⟩, ⟨_, fA⟩, _⟩, ⟨_, hc, _⟩, _⟩,
      ⟨o₄, ht, fT⟩, _⟩, b, f, bp, si, sp, rd, wr⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, ⟨_, _, ⟨o₁, _⟩, _⟩, _, _, e₁, _⟩ ⟨_, ⟨_, _, ⟨o₂, _⟩, _⟩, _, _, e₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁, e₂, o₁.env.ebp, o₂.env.ebp]) (by taint_decide)
  have esp := pubSw_esp hpub
  have a : ∀ i, i < 8 → arg s₀ i = p.2 i := fun i hi => pubSw_arg hpub (by omega) (by omega) (by omega)
  have tS : ∀ r ∈ [(⟨w64 (p.2 9), 16⟩ : Region)], (savedR (p.2 8)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (tw.sub_right (Lay.wSub (by decide))).symm
  have tR : ∀ r ∈ [(⟨w64 (p.2 9), 16⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact rt
  refine WP.mono (exit_ok (W := p.2 8) (by rw [bp, o₄.env.ebp]) (by rw [sp, o₄.env.esp, esp])
    (by rw [rd, wr]; exact covers_left o₄.env.wW) L.fw (o₄.saved.frame f tS)
    (by rw [esp, ret_kept f tR]; exact o₄.ret)) fun s' ⟨abi, m', _, _, _⟩ => ⟨abi, ?_⟩
  have hD₂ : bytesAt s₂.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat := by
    rw [bytesAt_frame fA (VG.Proof.AesGcm.X86.d_oF G) (by have := G.fd; omega)]; exact hE.data
  have hD₄ : bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₃.mem (w64 (p.2 6)) (p.2 7).toNat :=
    bytesAt_frame (oT_oF fT) (VG.Proof.AesGcm.X86.d_woF G (by decide)) (by have := G.fd; omega)
  have hD₅ : bytesAt s''.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat :=
    bytesAt_frame f (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dt) (by have := G.fd; omega)
  have hcg : gctr (ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat) (inc32 (jOf p s₀))
      (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat) = bytesAt s₃.mem (w64 (p.2 6)) (p.2 7).toNat := by
    rw [hc, hD₂, Proof.Gcm.gctr_eq]
  simp only [sealX86]
  rw [a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide), a 5 (by decide),
    a 6 (by decide), a 7 (by decide), a8 hpub, m']
  simp only [encryptWith]
  rw [hcg, hD₅, hD₄, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  rw [b, ht, Proof.Gcm.fullTag_eq, VG.Proof.AesGcm.X86.toBytes_take16, VG.Proof.AesGcm.X86.padded_eq, length_bytesAt, length_bytesAt]

theorem seal_correct (s : State) (hs : sealX86.pre s) :
    ∃ t s', Exec isa («seal» vg.callees) s t s' ∧ abiPreserved s s' ∧ sealX86.post s s' :=
  (VG.Proof.AesGcm.X86.seal_pc (pubSw 10 8 s)).wp s s ⟨hs, rfl, rfl⟩

theorem seal_ct : ConstantTime isa sealX86.pre sealX86.pub («seal» vg.callees) :=
  Pc.constantTime (pubSw 10 8) (fun _ _ _ _ h => pubSw_eq (by decide) h) VG.Proof.AesGcm.X86.seal_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Open`. -/
section

/-!
# AES-GCM on x86: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. The entry (`oneEntry_pc`,
keeping `tag_len` too), the tag length checked (`tagLenOk_pc`), and then
either nothing, or `J₀` and the additional data (`oneAad_pc`), the tag of
the ciphertext into `W + 112` (`oneTag_pc`), the received tag copied
(`recv_ok`) and compared (`cmp_ok`) without a branch, and the data decrypted
(`oneCrypt_pc`) if they are equal, as one `Pc` (`open_pc`): correct
(`open_correct`) and constant time but for whether the tag is right
(`open_ct`), which the contract lets it leak: the index of the `Pc` is the
public data and that bit.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph zeros padLen inc32 ghash ghashFrom blocks toBytes ofBytes gctr
  fullTag openResult decryptWith)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

/-- What `open` computes, in terms of the public data `p`. -/
abbrev oRes (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : Option (List Byte) :=
  openResult (ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat) (ctxH s₀.mem (w64 (p.2 0))) (p.2 9).toNat
    (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat) (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat)
    (bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat) (bytesAt s₀.mem (w64 (p.2 10)) (p.2 9).toNat)

/-- The arguments of `open`, in its public data (`W` at 8, `tag` at 10). -/
theorem open_arg {s₀ : State} {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubSw 11 8 s₀ = p) {i : Nat}
    (hi : i < 8 ∨ i = 9) : arg s₀ i = p.2 i :=
  pubSw_arg hp (by omega) (by omega) (by omega)

theorem open_tag {s₀ : State} {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubSw 11 8 s₀ = p) : arg s₀ 8 = p.2 10 :=
  pubSw_last hp (by decide) rfl

theorem openRes_eq {s₀ : State} {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubSw 11 8 s₀ = p) :
    openRes s₀ = VG.Proof.AesGcm.X86.oRes p s₀ := by
  simp only [openRes, VG.Proof.AesGcm.X86.oRes, VG.Proof.AesGcm.X86.open_arg hp (i := 0) (by decide), VG.Proof.AesGcm.X86.open_arg hp (i := 1) (by decide),
    VG.Proof.AesGcm.X86.open_arg hp (i := 2) (by decide), VG.Proof.AesGcm.X86.open_arg hp (i := 3) (by decide), VG.Proof.AesGcm.X86.open_arg hp (i := 4) (by decide),
    VG.Proof.AesGcm.X86.open_arg hp (i := 5) (by decide), VG.Proof.AesGcm.X86.open_arg hp (i := 6) (by decide), VG.Proof.AesGcm.X86.open_arg hp (i := 7) (by decide),
    VG.Proof.AesGcm.X86.open_tag hp, VG.Proof.AesGcm.X86.open_arg hp (i := 9) (by decide)]

/-- The tag of the message, and the tag received. -/
abbrev tagOf (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : List Byte :=
  fullTag (ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat) (ctxH s₀.mem (w64 (p.2 0)))
    (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat) (bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat)
    (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat)

abbrev rcvOf (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : List Byte :=
  bytesAt s₀.mem (w64 (p.2 10)) (p.2 9).toNat

theorem oRes_ok {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (ht : Spec.Gcm.tagLenOk (p.2 9).toNat = true) :
    VG.Proof.AesGcm.X86.oRes p s₀ = if (VG.Proof.AesGcm.X86.tagOf p s₀).take (p.2 9).toNat = VG.Proof.AesGcm.X86.rcvOf p s₀ then
      some (gctr (ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat) (inc32 (jOf p s₀))
        (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat)) else none := by
  simp only [VG.Proof.AesGcm.X86.oRes, openResult, ht, ↓reduceIte, decryptWith]

theorem oRes_bad {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (ht : Spec.Gcm.tagLenOk (p.2 9).toNat = false) :
    VG.Proof.AesGcm.X86.oRes p s₀ = none := by
  simp only [VG.Proof.AesGcm.X86.oRes, openResult, ht, Bool.false_eq_true, ↓reduceIte]

/-- What is fixed of a run of `open` for the index `q`: the public data, and
whether it returns 1. -/
structure IX (q : (BitVec 32 × (Nat → BitVec 32)) × Bool) (s₀ : State) : Prop where
  pre : openPre s₀
  pub : pubSw 11 8 s₀ = q.1
  res : (VG.Proof.AesGcm.X86.oRes q.1 s₀).isSome = q.2

theorem IX.q2 {q : (BitVec 32 × (Nat → BitVec 32)) × Bool} {s₀ : State} (h : VG.Proof.AesGcm.X86.IX q s₀)
    (ht : Spec.Gcm.tagLenOk (q.1.2 9).toNat = true) :
    q.2 = decide ((VG.Proof.AesGcm.X86.tagOf q.1 s₀).take (q.1.2 9).toNat = VG.Proof.AesGcm.X86.rcvOf q.1 s₀) := by
  rw [← h.res, VG.Proof.AesGcm.X86.oRes_ok ht]
  split <;> simp_all

/-- What `open` returns, before the exit. -/
def PostO (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop :=
  match VG.Proof.AesGcm.X86.oRes p s₀ with
  | some pt => s.gpr .eax = 1 ∧ bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat = pt
  | none => s.gpr .eax = 0 ∧
    bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

/-- `OEnt`, after code that keeps the memory and the registers it pins. -/
theorem OEnt.same {s₀ s s' : State} (h : OEnt p s₀ s) (hm : s'.mem = s.mem) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    OEnt p s₀ s' :=
  ⟨h.o.frame G (by rw [hm]; exact Frame.refl _ _) hbp hsi hsp hrd hwr, by rw [hm]; exact h.dO,
    by rw [hm]; exact h.nO, by rw [hm]; exact h.iv, by rw [hm]; exact h.data, by rw [hm]; exact h.frame⟩

/-- A kept slot, apart from the tag at `W + o` and what the pieces write. -/
theorem kept_woF {o n o' : Nat} (h₁ : 128 ≤ o)
    (h₂ : o + n ≤ auxO ∨ (auxO + 4 ≤ o ∧ o + n ≤ rO) ∨ (rO + 16 ≤ o ∧ o + n ≤ 240))
    (ho' : o' + 16 ≤ 128) :
    ∀ r ∈ ⟨w64 (p.2 8) + BitVec.ofNat 64 o', 16⟩ :: oF p,
      (⟨w64 (p.2 8) + BitVec.ofNat 64 o, n⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [auxO, rO] at h₂
    exact Lay.w_w (.inr (by omega)) (by omega) (by omega)
  · exact slot_oF G h₁ h₂ r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

omit G in
/-- A region apart from `W` and the stack the calls use, apart from what the pieces write. -/
theorem t_woF {o : Nat} (ho : o + 16 ≤ 2560) {T : Region} (tw : T.Disjoint ⟨w64 (p.2 8), 2560⟩)
    (kt : (below p.1 28).Disjoint T) : ∀ r ∈ ⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: oF p, T.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact tw.sub_right (Lay.wSub ho)
  · exact tw.sub_right (Lay.wSub (by decide))
  · exact tw.sub_right (Lay.wSub (by decide))
  · exact tw.sub_right (Lay.wSub (by decide))
  · exact tw.sub_right (Lay.wSub (by decide))
  · exact kt.symm

/-- The counter block, apart from a part of `W` from `W + 80` on. -/
theorem st48_w {o k : Nat} (h : 80 ≤ o) (hk : o + k ≤ 2560) :
    (⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨w64 (p.2 8) + BitVec.ofNat 64 o, k⟩ := by
  rw [st_eq G]; exact Lay.w_w (.inl (by omega)) (by decide) hk

end

/-- After the received tag is compared and the result kept at `W + auxO`. -/
structure OC (q : (BitVec 32 × (Nat → BitVec 32)) × Bool) (s₀ s : State) : Prop where
  o : OEnv q.1 s₀ s
  ix : VG.Proof.AesGcm.X86.IX q s₀
  aux : slotv s.mem (q.1.2 8) auxO = BitVec.ofNat 32 (if q.2 = true then 1 else 0)
  zf : s.zf = some (!q.2)
  cb : blockAt s.mem (w64 (stOf (q.1.2 8)) + BitVec.ofNat 64 48) = inc32 (jOf q.1 s₀)
  data : bytesAt s.mem (w64 (q.1.2 6)) (q.1.2 7).toNat = bytesAt s₀.mem (w64 (q.1.2 6)) (q.1.2 7).toNat

/-- After the data is decrypted if the tag is right. -/
structure OD (q : (BitVec 32 × (Nat → BitVec 32)) × Bool) (s₀ s : State) : Prop where
  o : OEnv q.1 s₀ s
  ix : VG.Proof.AesGcm.X86.IX q s₀
  aux : slotv s.mem (q.1.2 8) auxO = BitVec.ofNat 32 (if q.2 = true then 1 else 0)
  data : bytesAt s.mem (w64 (q.1.2 6)) (q.1.2 7).toNat = if q.2 = true then
    gctr (ctxCiph s₀.mem (w64 (q.1.2 0)) (q.1.2 1).toNat) (inc32 (jOf q.1 s₀))
      (bytesAt s₀.mem (w64 (q.1.2 6)) (q.1.2 7).toNat) else bytesAt s₀.mem (w64 (q.1.2 6)) (q.1.2 7).toNat

theorem open_eq : («open» vg.callees) = .seq (oneEntry 10 ([(8, tpO), (9, tglO)].flatMap
    (fun (p : Nat × Nat) => VG.Impl.AesGcm.X86.keep p.1 p.2))) (.seq tagLenOk (.seq (.ite .e (.block [.mov .eax (imm 0)])
    (.seq (oneAad vg.callees) (.seq (oneTag vg.callees uO) (.seq recv (.seq (cmp uO)
      (.seq (.block [.store (at_ .ebp auxO) .eax, .alu .test .eax (.reg .eax)])
      (.seq (.ite .e (.block []) (oneCrypt vg.callees)) (.block [.mov .eax (slot auxO)]))))))))
    (.block restore))) := rfl

theorem open_pc (q : (BitVec 32 × (Nat → BitVec 32)) × Bool) :
    Pc (fun (s₀ : State) s => openPre s₀ ∧ (pubSw 11 8 s₀, (openRes s₀).isSome) = q ∧ s = s₀) («open» vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ openX86.post s₀ s') := by
  by_cases hex : ∃ s₀, openPre s₀ ∧ (pubSw 11 8 s₀, (openRes s₀).isSome) = q
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzq⟩ := hex
  have hzp : pubSw 11 8 z = q.1 := by rw [← hzq]
  have G : OL q.1 := (op_of_open hz).ol rfl (by decide) hzp
  have L := G.L
  obtain ⟨-, ftg, tw, kt⟩ := openPre_tag hz
  rw [VG.Proof.AesGcm.X86.open_tag hzp, VG.Proof.AesGcm.X86.open_arg hzp (i := 9) (by decide)] at ftg
  rw [VG.Proof.AesGcm.X86.open_tag hzp, VG.Proof.AesGcm.X86.open_arg hzp (i := 9) (by decide), pubSw_W hzp (m := 10) (by decide) rfl] at tw
  rw [VG.Proof.AesGcm.X86.open_tag hzp, VG.Proof.AesGcm.X86.open_arg hzp (i := 9) (by decide), pubSw_esp hzp] at kt
  have ht32 : (q.1.2 9).toNat < 2 ^ 32 := (q.1.2 9).isLt
  generalize hok : Spec.Gcm.tagLenOk (q.1.2 9).toNat = ok
  rw [VG.Proof.AesGcm.X86.open_eq]
  -- The entry.
  refine Pc.seq (Pc.mono (oneEntry_pc 11 10 rfl (by decide) [(8, tpO), (9, tglO)] (by decide) (by decide) (by simp)
    (fun s₀ => openPre s₀ ∧ (openRes s₀).isSome = q.2) (fun _ h => op_of_open h.1) q.1 G (by taint_decide)
    (by taint_decide))
    (fun s₀ s ⟨h₁, hq, hs⟩ => ⟨⟨h₁, by rw [← hq]⟩, by rw [← hq], hs⟩) (fun _ _ h => h)) ?_
  -- The tag length.
  refine Pc.seq (Q := fun s₀ s => OEnt q.1 s₀ s ∧
      slotv s.mem (q.1.2 8) tglO = BitVec.ofNat 32 (q.1.2 9).toNat ∧ VG.Proof.AesGcm.X86.IX q s₀ ∧ s.zf = some (!ok))
    (Pc.mono (Pc.lift (tagLenOk_pc (W := q.1.2 8) ht32) (fun _ s => s) fun s₀ s ⟨h, ht, hp, _⟩ =>
      ⟨rfl, h.o.env.ebp, L.aW (by decide), h.o.env.wIn' (by decide), by
        rw [ht (9, tglO) (by simp), VG.Proof.AesGcm.X86.open_arg hp (i := 9) (by decide), ofNat_toNat32]⟩) (fun _ _ h => h)
      fun s₀ s ⟨s₁, ⟨h, ht, hp, hpre, hres⟩, ⟨tl, hzf⟩, _, _⟩ =>
        ⟨h.same G tl.mem (tl.other _ (by decide) (by decide)) (tl.other _ (by decide) (by decide))
          (tl.other _ (by decide) (by decide)) tl.rd tl.wr,
          by rw [tl.mem, ht (9, tglO) (by simp), VG.Proof.AesGcm.X86.open_arg hp (i := 9) (by decide), ofNat_toNat32],
          ⟨hpre, hp, by rw [← VG.Proof.AesGcm.X86.openRes_eq hp]; exact hres⟩, by rw [hzf, hok]⟩) ?_
  refine Pc.seq (Q := fun s₀ s => OEnv q.1 s₀ s ∧ VG.Proof.AesGcm.X86.IX q s₀ ∧ VG.Proof.AesGcm.X86.PostO q.1 s₀ s)
    (Pc.ite (!ok) (fun _ _ h => h.2.2.2) (fun hb => ?_) (fun hb => ?_)) ?_
  -- A tag length §5.2.1.2 does not allow.
  · have hf : ok = false := by simpa using hb
    refine Pc.taint [.ebp] (fun s₀ s ⟨h, _, hx, _⟩ => WP.of_runBlock ⟨_, by xrun [], ?_⟩)
      (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)
    refine ⟨h.o.frame G (by mems []; exact Frame.refl _ _) (by regs []) (by regs []) (by regs []) (by mems [])
      (by mems []), hx, ?_⟩
    simp only [VG.Proof.AesGcm.X86.PostO, VG.Proof.AesGcm.X86.oRes_bad (show Spec.Gcm.tagLenOk (q.1.2 9).toNat = false by rw [hok, hf])]
    exact ⟨by regs []; rfl, by mems []; exact h.data⟩
  -- An allowed one.
  have hT : ok = true := by simpa using hb
  have hT' : Spec.Gcm.tagLenOk (q.1.2 9).toNat = true := by rw [hok, hT]
  have ht' : 1 ≤ (q.1.2 9).toNat ∧ (q.1.2 9).toNat ≤ 16 := by
    have := hT'
    simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
    omega
  obtain ⟨t1, t16⟩ := ht'
  -- `J₀` and the additional data; the tag of the ciphertext.
  refine Pc.seq (Pc.lift (oneAad_pc G) (fun s₀ s => (s₀, s)) fun s₀ s h => ⟨h.1, rfl⟩) ?_
  refine Pc.seq (Pc.lift (oneTag_pc G (o := 112) (.inr rfl)) (fun s₀ s => (s₀, s))
    fun s₀ s ⟨_, _, ⟨ha, _⟩, _⟩ => ⟨⟨ha.o, ha.j, ha.y⟩, rfl⟩) ?_
  -- The received tag copied.
  have tgl : ∀ {sA s₂ s₃ : State}, slotv sA.mem (q.1.2 8) tglO = BitVec.ofNat 32 (q.1.2 9).toNat →
      Frame (oF q.1) sA.mem s₂.mem → Frame (oT q.1 112) s₂.mem s₃.mem →
      slotv s₃.mem (q.1.2 8) tglO = BitVec.ofNat 32 (q.1.2 9).toNat := fun hs fA fT => by
    rw [slotv_eq, slot_frame (oT_oF fT) (VG.Proof.AesGcm.X86.kept_woF G (o := tglO) (by decide) (.inl (by decide)) (by decide)),
      slot_frame fA fun r hr => slot_oF G (o := tglO) (by decide) (.inl (by decide)) r
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)), ← slotv_eq]
    exact hs
  refine Pc.seq (Pc.of (I := fun s => WEnv (q.1.2 8) s ∧
      slotv s.mem (q.1.2 8) tglO = BitVec.ofNat 32 (q.1.2 9).toNat ∧ slotv s.mem (q.1.2 8) tpO = q.1.2 10 ∧
      Covers [⟨w64 (q.1.2 10), (q.1.2 9).toNat⟩] (s.rd ++ s.wr))
    (R := fun s s' => bytesAt s'.mem (w64 (q.1.2 8) + BitVec.ofNat 64 rO) 16 =
        bytesAt s.mem (w64 (q.1.2 10)) (q.1.2 9).toNat ++ zeros (16 - (q.1.2 9).toNat) ∧
      Frame [⟨w64 (q.1.2 8) + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (fun s hs => recv_ok hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 ftg tw t1 t16)
    (recv_ct fun s hs => ⟨hs.1, hs.2.1, hs.2.2.1⟩) _
    (fun s₀ s₃ ⟨s₂, ⟨sA, ⟨_, hs, hx, _⟩, ⟨_, fA⟩, _⟩, ⟨o₃, _, fT⟩, _⟩ =>
      ⟨⟨o₃.env.ebp, o₃.env.wW, L.fw⟩, tgl hs fA fT, by rw [o₃.tp, VG.Proof.AesGcm.X86.open_tag hx.pub], by
        rw [o₃.rd, o₃.wr, ← VG.Proof.AesGcm.X86.open_tag hx.pub, ← VG.Proof.AesGcm.X86.open_arg hx.pub (i := 9) (by decide)]
        exact (openPre_tag hx.pre).1⟩)) ?_
  -- Compared.
  have rR_tgl : ∀ {s s' : State}, Frame [⟨w64 (q.1.2 8) + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem →
      slotv s'.mem (q.1.2 8) tglO = slotv s.mem (q.1.2 8) tglO := fun f => by
    rw [slotv_eq, slotv_eq]
    exact slot_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine Pc.seq (Pc.of (I := fun s => WEnv (q.1.2 8) s ∧
      slotv s.mem (q.1.2 8) tglO = BitVec.ofNat 32 (q.1.2 9).toNat)
    (R := fun s s' => s'.gpr .eax = BitVec.ofNat 32
        (if bytesAt s.mem (w64 (q.1.2 8) + BitVec.ofNat 64 uO) (q.1.2 9).toNat ++ zeros (16 - (q.1.2 9).toNat) =
            bytesAt s.mem (w64 (q.1.2 8) + BitVec.ofNat 64 rO) 16 then 1 else 0) ∧
      Frame [⟨w64 (q.1.2 8) + BitVec.ofNat 64 vO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (fun s hs => cmp_ok hs.1 hs.2 t1 t16 (by decide)) (cmp_ct (.inr rfl) fun s hs => hs) _
    (fun s₀ s₄ ⟨s₃, ⟨s₂, ⟨sA, ⟨_, hs, _⟩, ⟨_, fA⟩, _⟩, ⟨o₃, _, fT⟩, _⟩, ⟨_, f₄, bp₄, _, _, _, wr₄⟩⟩ =>
      ⟨⟨by rw [bp₄, o₃.env.ebp], by rw [wr₄]; exact o₃.env.wW, L.fw⟩, by rw [rR_tgl f₄]; exact tgl hs fA fT⟩)) ?_
  -- The result kept, and tested.
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.OC q) (Pc.taint [.ebp] (fun s₀ s₅ hk => ?_)
    (fun _ _ s₁ s₂ ⟨_, ⟨_, ⟨_, _, ⟨o₁, _⟩, _⟩, _, _, e₁, _⟩, _, _, e₁', _⟩
      ⟨_, ⟨_, ⟨_, _, ⟨o₂, _⟩, _⟩, _, _, e₂, _⟩, _, _, e₂', _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁', e₁, e₂', e₂, o₁.env.ebp, o₂.env.ebp])
    (by taint_decide)) ?_
  · obtain ⟨s₄, ⟨s₃, ⟨s₂, ⟨sA, ⟨hE, _, hx, _⟩, ⟨ha, fA⟩, _⟩, ⟨o₃, ht, fT⟩, _⟩,
      ⟨b₄, f₄, bp₄, si₄, sp₄, rd₄, wr₄⟩⟩, ⟨a₅, f₅, bp₅, si₅, sp₅, rd₅, wr₅⟩⟩ := hk
    have fo₄ : Frame (oF q.1) s₃.mem s₄.mem := f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    have fo₅ : Frame (oF q.1) s₄.mem s₅.mem := f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wsR (q.1.2 8), by simp, Offset.sub _ (by decide) (by decide)⟩
    have o₅ := (o₃.frame G (Frame.oD fo₄) bp₄ si₄ sp₄ rd₄ wr₄).frame G (Frame.oD fo₅) bp₅ si₅ sp₅ rd₅ wr₅
    -- The tags.
    have hc₂ : bytesAt s₂.mem (w64 (q.1.2 6)) (q.1.2 7).toNat = bytesAt s₀.mem (w64 (q.1.2 6)) (q.1.2 7).toNat := by
      rw [bytesAt_frame fA (VG.Proof.AesGcm.X86.d_oF G) (by have := G.fd; omega)]; exact hE.data
    have hT₃ : bytesAt s₃.mem (w64 (q.1.2 8) + BitVec.ofNat 64 uO) 16 = VG.Proof.AesGcm.X86.tagOf q.1 s₀ := by
      dsimp only at ht
      rw [ht, hc₂, VG.Proof.AesGcm.X86.tagOf, Proof.Gcm.fullTag_eq, VG.Proof.AesGcm.X86.padded_eq, length_bytesAt, length_bytesAt]
    have hT₄ : bytesAt s₄.mem (w64 (q.1.2 8) + BitVec.ofNat 64 uO) (q.1.2 9).toNat =
        (VG.Proof.AesGcm.X86.tagOf q.1 s₀).take (q.1.2 9).toNat := by
      rw [← bytesAt_take _ _ t16, bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), hT₃]
    have hw₃ : bytesAt s₃.mem (w64 (q.1.2 10)) (q.1.2 9).toNat = VG.Proof.AesGcm.X86.rcvOf q.1 s₀ := by
      have ht₁ : (q.1.2 9).toNat ≤ 2 ^ 64 := by omega
      rw [bytesAt_frame (oT_oF fT) (VG.Proof.AesGcm.X86.t_woF (by decide) tw kt) ht₁,
        bytesAt_frame fA (fun r hr => VG.Proof.AesGcm.X86.t_woF (o := 0) (by decide) tw kt r (List.mem_cons_of_mem _ hr)) ht₁,
        bytesAt_frame hE.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact tw.sub_right (Lay.wSub (by decide))) ht₁]
    have hR₄ : bytesAt s₄.mem (w64 (q.1.2 8) + BitVec.ofNat 64 rO) 16 =
        VG.Proof.AesGcm.X86.rcvOf q.1 s₀ ++ zeros (16 - (q.1.2 9).toNat) := by
      rw [b₄, hw₃]
    have hq2 := hx.q2 hT'
    have a₅' : s₅.gpr .eax = BitVec.ofNat 32 (if q.2 = true then 1 else 0) := by
      rw [a₅, hT₄, hR₄, hq2]
      by_cases h : (VG.Proof.AesGcm.X86.tagOf q.1 s₀).take (q.1.2 9).toNat = VG.Proof.AesGcm.X86.rcvOf q.1 s₀
      · simp only [h, List.append_left_inj, decide_true, ↓reduceIte]
      · simp only [h, List.append_left_inj, decide_false, Bool.false_eq_true, ↓reduceIte]
    have aW := o₅.env.wIn (d := auxO) (n := 4) (by decide)
    refine WP.of_runBlock ⟨_, by xrun [o₅.env.ebp, L.aW, aW], ?_⟩
    have fx : Frame (oF q.1) s₅.mem (s₅.mem.writeW (w64 (q.1.2 8) + BitVec.ofNat 64 auxO) (s₅.gpr .eax)) :=
      (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    have fx₁ : Frame [⟨w64 (q.1.2 8) + BitVec.ofNat 64 auxO, 4⟩] s₅.mem
        (s₅.mem.writeW (w64 (q.1.2 8) + BitVec.ofNat 64 auxO) (s₅.gpr .eax)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have sg : ∀ {o : Nat}, 80 ≤ o → o + 16 ≤ 2560 → ∀ r ∈ [(⟨w64 (q.1.2 8) + BitVec.ofNat 64 o, 16⟩ : Region)],
        (⟨w64 (stOf (q.1.2 8)) + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesGcm.X86.st48_w G h₁ h₂
    refine ⟨o₅.frame G (by mems []; exact Frame.oD fx) (by regs []) (by regs []) (by regs []) (by mems [])
      (by mems []), hx, by mems [slotv_eq]; exact a₅', ?_, ?_, ?_⟩
    · mems []
      rw [a₅']
      cases q.2 <;> rfl
    · mems []
      rw [blockAt_frame fx₁ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesGcm.X86.st48_w G (by decide) (by decide),
        blockAt_frame f₅ (sg (by decide) (by decide)), blockAt_frame f₄ (sg (by decide) (by decide)),
        blockAt_frame fT (cb_oT G (.inr rfl))]
      exact ha.cb
    · mems []
      rw [bytesAt_frame fx₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact G.d_w.sub_right (Lay.wSub (by decide)))
          (by have := G.fd; omega),
        bytesAt_frame fo₅ (VG.Proof.AesGcm.X86.d_oF G) (by have := G.fd; omega), bytesAt_frame fo₄ (VG.Proof.AesGcm.X86.d_oF G) (by have := G.fd; omega),
        bytesAt_frame (oT_oF fT) (VG.Proof.AesGcm.X86.d_woF G (by decide)) (by have := G.fd; omega)]
      exact hc₂
  -- The data decrypted if the tags are equal.
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.OD q) (Pc.ite (!q.2) (fun _ _ h => h.zf) (fun hb => ?_) (fun hb => ?_)) ?_
  · have hf : q.2 = false := by simpa using hb
    refine Pc.mono Pc.nil (fun _ _ h => h) fun s₀ s h => ⟨h.o, h.ix, h.aux, ?_⟩
    rw [hf]; exact h.data
  · have ht : q.2 = true := by simpa using hb
    refine Pc.mono (Pc.lift (oneCrypt_pc G (fun s₀ => inc32 (jOf q.1 s₀))) (fun s₀ s => (s₀, s))
      fun s₀ s h => ⟨⟨h.o, Proof.Gcm.ctr_zero _ _ _ _ h.cb⟩, rfl⟩) (fun _ _ h => h)
      fun s₀ s' ⟨s, h, ⟨o', hd, fC⟩, _⟩ => ⟨o', h.ix, ?_, ?_⟩
    · rw [slotv_eq, slot_frame fC fun r hr => ?_, ← slotv_eq]
      · exact h.aux
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (G.d_w.sub_right (Lay.wSub (by decide))).symm
        · rw [st_eq G]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w (by decide)).symm
    · rw [hd, h.data, ht, Proof.Gcm.gctr_eq]; rfl
  -- The result.
  refine Pc.taint [.ebp] (fun s₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)
  have aR := h.o.env.wIn' (d := auxO) (n := 4) (by decide)
  have hv := h.aux
  rw [slotv_eq] at hv
  simp only [auxO] at hv aR
  refine WP.of_runBlock ⟨_, by xrun [h.o.env.ebp, L.aW, aR, hv], ?_⟩
  refine ⟨h.o.frame G (by mems []; exact Frame.refl _ _) (by regs []) (by regs []) (by regs []) (by mems [])
    (by mems []), h.ix, ?_⟩
  have hq2 := h.ix.q2 hT'
  simp only [VG.Proof.AesGcm.X86.PostO, VG.Proof.AesGcm.X86.oRes_ok hT']
  by_cases hX : (VG.Proof.AesGcm.X86.tagOf q.1 s₀).take (q.1.2 9).toNat = VG.Proof.AesGcm.X86.rcvOf q.1 s₀
  · have h2 : q.2 = true := by rw [hq2]; simpa using hX
    have := h.data
    rw [h2] at this
    simp only [hX, ↓reduceIte, h2]
    exact ⟨by regs []; rfl, by mems []; simpa using this⟩
  · have h2 : q.2 = false := by rw [hq2]; simpa using hX
    have := h.data
    rw [h2] at this
    simp only [hX, ↓reduceIte, h2]
    exact ⟨by regs []; rfl, by mems []; simpa using this⟩
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s ⟨o, hx, hpost⟩ => ?_) (fun _ _ s₁ s₂ ⟨o₁, _⟩ ⟨o₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [o₁.env.ebp, o₂.env.ebp]) (by taint_decide)
  have esp := pubSw_esp hx.pub
  refine WP.mono (exit_ok o.env.ebp (by rw [o.env.esp, esp]) (covers_left o.env.wW) L.fw o.saved
    (by rw [esp]; exact o.ret)) fun s' ⟨abi, m', ax, _, _⟩ => ⟨abi, ?_⟩
  simp only [openX86, ret32_eq]
  rw [VG.Proof.AesGcm.X86.openRes_eq hx.pub, VG.Proof.AesGcm.X86.open_arg hx.pub (i := 6) (by decide), VG.Proof.AesGcm.X86.open_arg hx.pub (i := 7) (by decide), m', ax]
  exact hpost

theorem open_correct (s : State) (hs : openX86.pre s) :
    ∃ t s', Exec isa («open» vg.callees) s t s' ∧ abiPreserved s s' ∧ openX86.post s s' :=
  (VG.Proof.AesGcm.X86.open_pc (pubSw 11 8 s, (openRes s).isSome)).wp s s ⟨hs, rfl, rfl⟩

theorem open_ct : ConstantTime isa openX86.pre openX86.pub («open» vg.callees) :=
  Pc.constantTime (fun s => (pubSw 11 8 s, (openRes s).isSome))
    (fun _ _ _ _ h => by rw [pubSw_eq (by decide) h.1, h.2]) VG.Proof.AesGcm.X86.open_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.StreamEncrypt`. -/
section

/-!
# AES-GCM on x86: `vg_aes_gcm_stream_encrypt`

Untrusted: everything here is checked by Lean. The entry, the text
encrypted (`crypt`), the ciphertext absorbed (`textAbsorb`) and the exit,
as one `Pc` (`streamEncrypt_pc`): correct (`streamEncrypt_correct`) and
constant time (`streamEncrypt_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph gctr inc32 j0)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem streamEncrypt_eq : (streamEncrypt vg.callees) = .seq (entry 9 (([.mov .esi (argOp 2)] : List Instr) ++
    (crKeeps.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ [])))
    (.seq (.block setText) (.seq (crypt vg.callees) (.seq (textAbsorb vg.callees) (.block restore)))) := rfl

/-- After `setText`: the text ready for `crypt`. -/
structure CSet (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  ent : ∃ s₁, CEnt p s₀ s₁ ∧ Frame [pslotR (p.2 9)] s₁.mem s.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr
  cr : CrIn (p.2 0) (p.2 2) (p.2 9) p.1 28 (p.2 1).toNat (p.2 7) (p.2 8).toNat (p.2 6 ++ p.2 5).toNat s

theorem cr_dataW {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {s₀ s : State} (hpre : streamCryptPre s₀)
    (hpub : pubOf 10 s₀ = p) (hwr : s.wr = s₀.wr) :
    DataW (p.2 0) (p.2 2) (p.2 9) p.1 28 s (p.2 7) (p.2 8).toNat := by
  have hp := hpre
  simp only [streamCryptPre] at hp
  have hw : Covers [⟨w64 (p.2 7), (p.2 8).toNat⟩] s.wr := by
    rw [hwr, hp.2.1, ← pubOf_arg hpub (i := 7) (by decide), ← pubOf_arg hpub (i := 8) (by decide)]
    exact covers_of_mem (by simp)
  exact ⟨⟨covers_left hw, hc.fd, hc.dst, hc.dw, hc.dstk⟩, hw, hc.dctx⟩

theorem setText_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (CEnt p) (.block setText) (VG.Proof.AesGcm.X86.CSet p) := by
  refine Pc.taint [.ebp] (fun s₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have hc := crPure_of h.pre h.pub
  have L := hc.lay
  obtain ⟨s', run, d, n, b, fr, bp, si, sp, rd, wr⟩ := setText_ok L h.env h.ta
  refine WP.of_runBlock ⟨s', run, ⟨s, h, fr, rd, wr⟩, ?_⟩
  have kP : ∀ r ∈ [pslotR (p.2 9)], (keptR (p.2 9)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨h.env.keep bp si sp rd wr (slot_frame fr fun r hr => (kP r hr).sub_left (Offset.sub _ (by decide)
    (by decide))), d, n, by rw [b, append_toNat32]; congr 1; omega, (p.2 8).isLt,
    VG.Proof.AesGcm.X86.cr_dataW hc h.pre h.pub (by rw [wr, h.wr]), rounds_frame fr kP h.rounds⟩

/-- The streaming state's regions are apart from what `crypt` and `textAbsorb` write, but their own. -/
theorem st_crFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {d k : Nat} (hk : d + k ≤ 48) :
    ∀ r ∈ crFrame (p.2 2) (p.2 9) p.1 28 (p.2 7) (p.2 8).toNat,
      (⟨w64 (p.2 2) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  have L := hc.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hc.dst.sub_right (Lay.stSub (by omega))).symm
  · exact Lay.st_st (.inl (by omega)) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega)).symm

theorem st_taFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {d k : Nat}
    (hk : d + k ≤ 16 ∨ (48 ≤ d ∧ d + k ≤ 80)) :
    ∀ r ∈ taFrame (p.2 2) (p.2 9) p.1 28, (⟨w64 (p.2 2) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  have L := hc.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega)).symm

theorem ret_crFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) :
    ∀ r ∈ crFrame (p.2 2) (p.2 9) p.1 28 (p.2 7) (p.2 8).toNat, (⟨w64 p.1, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hc.r_d
  · exact hc.r_s.sub_right (Lay.stSub (by decide))
  · exact hc.r_w.sub_right (Lay.wSub (by decide))
  · exact ret_below hc.sp

theorem ret_taFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) :
    ∀ r ∈ taFrame (p.2 2) (p.2 9) p.1 28, (⟨w64 p.1, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hc.r_s.sub_right (Lay.stSub (by decide))
  · exact hc.r_w.sub_right (Lay.wSub (by decide))
  · exact hc.r_w.sub_right (Lay.wSub (by decide))
  · exact ret_below hc.sp

/-- The entry's and `setText`'s writes, within `W`. -/
theorem cset_frame {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ s : State} (h₁ : CEnt p s₀ s₁)
    (fr : Frame [pslotR (p.2 9)] s₁.mem s.mem) : Frame [⟨w64 (p.2 9) + BitVec.ofNat 64 96, 2464⟩] s₀.mem s.mem :=
  (h₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).trans (fr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

/-- The exit of `encrypt` and `decrypt`, after `crypt` and `textAbsorb` in either order. -/
theorem cr_exit {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {s₀ s₁ s : State} (h₁ : CEnt p s₀ s₁)
    (he : Env (p.2 0) (p.2 2) (p.2 9) p.1 s)
    (hf : Frame (pslotR (p.2 9) :: crFrame (p.2 2) (p.2 9) p.1 28 (p.2 7) (p.2 8).toNat ++
      taFrame (p.2 2) (p.2 9) p.1 28) s₁.mem s.mem) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  have L := hc.lay
  have esp := pubOf_esp h₁.pub
  have hsv : SavedAt s.mem (p.2 9) s₀ := h₁.saved.frameK hf fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Lay.w_w (a := 128) (n := 112) (d := 272) (k := 12) (.inl (by decide)) (by decide) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · exact kept_crFrame L (VG.Proof.AesGcm.X86.cr_dataW hc h₁.pre h₁.pub h₁.wr) r hr
    · exact kept_taFrame L r hr
  have rT : ∀ r ∈ pslotR (p.2 9) :: crFrame (p.2 2) (p.2 9) p.1 28 (p.2 7) (p.2 8).toNat ++
      taFrame (p.2 2) (p.2 9) p.1 28, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hc.r_w.sub_right (Lay.wSub (d := 272) (n := 12) (by decide))
    rcases List.mem_append.mp hr with hr | hr
    · exact VG.Proof.AesGcm.X86.ret_crFrame hc r hr
    · exact VG.Proof.AesGcm.X86.ret_taFrame hc r hr
  have rE : ∀ r ∈ [(⟨w64 (p.2 9) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, ret_kept hf rT, ret_kept h₁.frame rE]
  exact WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) L.fw hsv hret)
    fun s' ⟨abi, m', _, _, _⟩ => ⟨abi, m'⟩

theorem streamEncrypt_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamCryptPre s₀ ∧ pubOf 10 s₀ = p ∧ s = s₀) (streamEncrypt vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamEncryptX86.post s₀ s') := by
  by_cases hex : ∃ s₀, streamCryptPre s₀ ∧ pubOf 10 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have hc := crPure_of hz hzp
  have L := hc.lay
  rw [VG.Proof.AesGcm.X86.streamEncrypt_eq]
  refine Pc.seq (crEntry_pc p) (Pc.seq (VG.Proof.AesGcm.X86.setText_pc p) ?_)
  refine Pc.seq (Pc.lift (Pc.forall fun icb => crypt_pc L rfl (R := (p.2 1).toNat) (icb := icb) (D := p.2 7)
    (n := (p.2 8).toNat) (P := (p.2 6 ++ p.2 5).toNat)) (fun _ s => s.mem) fun s₀ s h => ⟨h.cr, rfl⟩) ?_
  refine Pc.seq (Pc.lift (textAbsorb_pc L (D := p.2 7) (n := (p.2 8).toNat) (al := p.2 3) (ah := p.2 4)
    (xl := p.2 5) (xh := p.2 6)) (fun _ s => s.mem) fun s₀ s' ⟨s, h, co, rd, wr⟩ => ⟨?_, rfl⟩) ?_
  · obtain ⟨s₁, h₁, fr, rd₁, wr₁⟩ := h.ent
    have dw := VG.Proof.AesGcm.X86.cr_dataW hc h₁.pre h₁.pub (s := s') (by rw [wr, wr₁, h₁.wr])
    refine ⟨(co default).env, (h₁.ta.frame fr fun r hr => ?_).frame (co default).frame
      (kept_crFrame L h.cr.data), (p.2 8).isLt, dw.ok⟩
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine Pc.taint [.ebp] (fun s₀ s₄ ⟨s₃, ⟨s₂, h₂, co, rd₃, wr₃⟩, ta, rd₄, wr₄⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  obtain ⟨s₁, h₁, fr, rd₁, wr₁⟩ := h₂.ent
  have hf : Frame (pslotR (p.2 9) :: crFrame (p.2 2) (p.2 9) p.1 28 (p.2 7) (p.2 8).toNat ++
      taFrame (p.2 2) (p.2 9) p.1 28) s₁.mem s₄.mem :=
    ((fr.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      ((co default).frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr))).trans
      (ta.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_right _ hr))
  refine WP.mono (VG.Proof.AesGcm.X86.cr_exit hc h₁ ta.env hf) fun s' ⟨abi, m'⟩ => ⟨abi, fun iv a pt hr hl hpt => ?_⟩
  have hA : ∀ i, i < 10 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  dsimp only
  rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide)] at hr
  rw [hA 3 (by decide), hA 4 (by decide)] at hl
  rw [hA 5 (by decide), hA 6 (by decide)] at hpt
  rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide), hA 7 (by decide), hA 8 (by decide), m']
  generalize hci : ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat = ciph at hr ⊢
  generalize hH : ctxH s₀.mem (w64 (p.2 0)) = H at hr ⊢
  have fW := VG.Proof.AesGcm.X86.cset_frame h₁ fr
  have hC2 : ciphOf s₂.mem (p.2 0) (p.2 1).toNat = ciph := by
    rw [← hci]; exact ciph_frame fW (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))) hc.rounds
  have hH2 : Hk s₂.mem (p.2 0) = H := by
    rw [← hH, ctxH_eq]; exact blockAt_frame fW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hr₂ := streamRepr_frame fW (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.sb) hr
  rw [← hC2, ← hH2] at hr₂
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hr₂
  obtain ⟨hj, ha, hct⟩ := hr₂
  rw [hH2] at hj
  rw [hC2, hH2] at ha hct
  have hP : (gctr ciph (inc32 (j0 H iv)) pt).length = (p.2 6 ++ p.2 5).toNat := by
    rw [Proof.Gcm.length_gctr, hpt]
  rw [hP] at hct
  have hco := co (inc32 (j0 H iv))
  have hct' : CtrS s₂.mem (p.2 2) (ciphOf s₂.mem (p.2 0) (p.2 1).toNat) (inc32 (j0 H iv))
      (p.2 6 ++ p.2 5).toNat := by rw [hC2]; exact hct
  have hct₃ := hco.ctr hct'
  have hout := hco.out hct'
  rw [hC2] at hct₃ hout
  have hd := h₂.cr.data
  have hfit := hd.ok.fit
  have hD2 : bytesAt s₂.mem (w64 (p.2 7)) (p.2 8).toNat = bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat :=
    bytesAt_frame fW (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.dw.sub_right (Lay.wSub (by decide))) (by omega)
  rw [hD2] at hout
  have hH3 : Hk s₃.mem (p.2 0) = H := by
    rw [← hH2]; exact blockAt_frame hco.frame fun r hr =>
      (ctx_crFrame L hd r hr).sub_left (Lay.ctxSub (by decide))
  have ha₃ : Absorbed s₃.mem (w64 (p.2 2) + BitVec.ofNat 64 16) (w64 (p.2 2) + BitVec.ofNat 64 32)
      (Hk s₃.mem (p.2 0)) (Spec.Gcm.ghashInput a (gctr ciph (inc32 (j0 H iv)) pt)) := by
    rw [hH3]
    exact ha.congr (blockAt_frame hco.frame (VG.Proof.AesGcm.X86.st_crFrame hc (by decide)))
      (bytesAt_frame hco.frame (VG.Proof.AesGcm.X86.st_crFrame hc (d := 32) (k := (Spec.Gcm.ghashInput a _).length % 16) (by omega))
        (by omega))
  have hab := ta.abs a (gctr ciph (inc32 (j0 H iv)) pt) ⟨hl, by rw [Proof.Gcm.length_gctr, hpt]⟩ ha₃
  rw [hout, hH3] at hab
  have hcnew : gctr ciph (inc32 (j0 H iv)) (pt ++ bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat) =
      gctr ciph (inc32 (j0 H iv)) pt ++
        xorKs ciph (inc32 (j0 H iv)) (p.2 6 ++ p.2 5).toNat (bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat) := by
    rw [Proof.Gcm.gctr_append, hpt]
  have dT := data_taFrame (D := p.2 7) (n := (p.2 8).toNat) hd.ok
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hcnew]
    refine ⟨?_, hab, ?_⟩
    · have e₁ := blockAt_frame ta.frame (VG.Proof.AesGcm.X86.st_taFrame hc (d := 0) (k := 16) (.inl (by decide)))
      have e₂ := blockAt_frame hco.frame (VG.Proof.AesGcm.X86.st_crFrame hc (d := 0) (k := 16) (by decide))
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e₁ e₂
      rw [e₁, e₂, hj]
    · rw [List.length_append, Proof.Gcm.length_gctr, Proof.Gcm.length_xorKs, length_bytesAt, ← hpt]
      exact hct₃.congr (blockAt_frame ta.frame (VG.Proof.AesGcm.X86.st_taFrame hc (.inr ⟨by decide, by decide⟩)))
        (blockAt_frame ta.frame (VG.Proof.AesGcm.X86.st_taFrame hc (.inr ⟨by decide, by decide⟩)))
  · rw [bytesAt_frame ta.frame dT (by omega), hout, hcnew,
      List.drop_left' (by rw [Proof.Gcm.length_gctr])]

theorem streamEncrypt_correct (s : State) (hs : streamEncryptX86.pre s) :
    ∃ t s', Exec isa (streamEncrypt vg.callees) s t s' ∧ abiPreserved s s' ∧ streamEncryptX86.post s s' :=
  (VG.Proof.AesGcm.X86.streamEncrypt_pc (pubOf 10 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamEncrypt_ct : ConstantTime isa streamEncryptX86.pre streamEncryptX86.pub (streamEncrypt vg.callees) :=
  Pc.constantTime (pubOf 10) (fun _ _ _ _ h => pubOf_eq h) VG.Proof.AesGcm.X86.streamEncrypt_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.StreamDecrypt`. -/
section

/-!
# AES-GCM on x86: `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry, the ciphertext
absorbed (`textAbsorb`), the text decrypted (`crypt`) and the exit, as one
`Pc` (`streamDecrypt_pc`): correct (`streamDecrypt_correct`) and constant
time (`streamDecrypt_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph gctr inc32 j0)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem streamDecrypt_eq : (streamDecrypt vg.callees) = .seq (entry 9 (([.mov .esi (argOp 2)] : List Instr) ++
    (crKeeps.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ [])))
    (.seq (textAbsorb vg.callees) (.seq (.block setText) (.seq (crypt vg.callees) (.block restore)))) := rfl

theorem streamDecrypt_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamCryptPre s₀ ∧ pubOf 10 s₀ = p ∧ s = s₀) (streamDecrypt vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamDecryptX86.post s₀ s') := by
  by_cases hex : ∃ s₀, streamCryptPre s₀ ∧ pubOf 10 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have hc := crPure_of hz hzp
  have L := hc.lay
  rw [VG.Proof.AesGcm.X86.streamDecrypt_eq]
  refine Pc.seq (crEntry_pc p) ?_
  refine Pc.seq (Pc.lift (textAbsorb_pc L (D := p.2 7) (n := (p.2 8).toNat) (al := p.2 3) (ah := p.2 4)
    (xl := p.2 5) (xh := p.2 6)) (fun _ s => s.mem) fun s₀ s h =>
      ⟨⟨h.env, h.ta, (p.2 8).isLt, (VG.Proof.AesGcm.X86.cr_dataW hc h.pre h.pub h.wr).ok⟩, rfl⟩) ?_
  -- The text, as `crypt` takes it.
  refine Pc.seq (Q := fun s₀ s₃ => ∃ s₂, (∃ s₁, CEnt p s₀ s₁ ∧
      TaOut (p.2 0) (p.2 2) (p.2 9) p.1 28 (p.2 7) (p.2 8).toNat (p.2 3) (p.2 4) (p.2 5) (p.2 6) s₁.mem s₂ ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr) ∧
      CrIn (p.2 0) (p.2 2) (p.2 9) p.1 28 (p.2 1).toNat (p.2 7) (p.2 8).toNat (p.2 6 ++ p.2 5).toNat s₃ ∧
      Frame [pslotR (p.2 9)] s₂.mem s₃.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr)
    (Pc.taint [.ebp] (fun s₀ s₂ h => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s₁, h₁, ta, rd₂, wr₂⟩ := h
    have sl := h₁.ta.frame ta.frame (kept_taFrame L)
    obtain ⟨s₃, run, d, n, b, fr, bp, si, sp, rd, wr⟩ := setText_ok L ta.env sl
    refine WP.of_runBlock ⟨s₃, run, s₂, ⟨s₁, h₁, ta, rd₂, wr₂⟩, ?_, fr, rd, wr⟩
    have kP : ∀ r ∈ [pslotR (p.2 9)], (keptR (p.2 9)).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    refine ⟨ta.env.keep bp si sp rd wr (slot_frame fr fun r hr => (kP r hr).sub_left (Offset.sub _ (by decide)
      (by decide))), d, n, by rw [b, append_toNat32]; congr 1; omega, (p.2 8).isLt,
      VG.Proof.AesGcm.X86.cr_dataW hc h₁.pre h₁.pub (by rw [wr, wr₂, h₁.wr]),
      rounds_frame fr kP (rounds_frame ta.frame (kept_taFrame L) h₁.rounds)⟩
  refine Pc.seq (Pc.lift (Pc.forall fun icb => crypt_pc L rfl (R := (p.2 1).toNat) (icb := icb) (D := p.2 7)
    (n := (p.2 8).toNat) (P := (p.2 6 ++ p.2 5).toNat)) (fun _ s => s.mem) fun s₀ s ⟨_, _, hin, _⟩ => ⟨hin, rfl⟩) ?_
  refine Pc.taint [.ebp] (fun s₀ s₄ ⟨s₃, ⟨s₂, ⟨s₁, h₁, ta, rd₂, wr₂⟩, hin, fr, rd₃, wr₃⟩, co, rd₄, wr₄⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h₁ default).env.ebp, (h₂ default).env.ebp])
    (by taint_decide)
  have hf : Frame (pslotR (p.2 9) :: crFrame (p.2 2) (p.2 9) p.1 28 (p.2 7) (p.2 8).toNat ++
      taFrame (p.2 2) (p.2 9) p.1 28) s₁.mem s₄.mem :=
    ((ta.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_right _ hr)).trans
      (fr.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..)).trans
      ((co default).frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr))
  refine WP.mono (VG.Proof.AesGcm.X86.cr_exit hc h₁ (co default).env hf) fun s' ⟨abi, m'⟩ => ⟨abi, fun iv a c hr hl hct => ?_⟩
  have hA : ∀ i, i < 10 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  dsimp only
  rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide)] at hr
  rw [hA 3 (by decide), hA 4 (by decide)] at hl
  rw [hA 5 (by decide), hA 6 (by decide)] at hct
  rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide), hA 7 (by decide), hA 8 (by decide), m']
  generalize hci : ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat = ciph at hr ⊢
  generalize hH : ctxH s₀.mem (w64 (p.2 0)) = H at hr ⊢
  have fE : Frame [⟨w64 (p.2 9) + BitVec.ofNat 64 96, 2464⟩] s₀.mem s₁.mem :=
    h₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hd := hin.data
  have hfit := hd.ok.fit
  have dP : ∀ r ∈ [pslotR (p.2 9)], (⟨w64 (p.2 7), (p.2 8).toNat⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.dw.sub_right (Lay.wSub (by decide))
  have hC1 : ciphOf s₁.mem (p.2 0) (p.2 1).toNat = ciph := by
    rw [← hci]; exact ciph_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))) hc.rounds
  have hC3 : ciphOf s₃.mem (p.2 0) (p.2 1).toNat = ciph := by
    rw [← hC1, ciph_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))) hc.rounds,
      ciph_frame ta.frame (ctx_taFrame L) hc.rounds]
  have hH1 : Hk s₁.mem (p.2 0) = H := by
    rw [← hH, ctxH_eq]; exact blockAt_frame fE fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hr₁ := streamRepr_frame fE (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.sb) hr
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hr₁
  obtain ⟨hj, ha, hcr⟩ := hr₁
  have hD1 : bytesAt s₁.mem (w64 (p.2 7)) (p.2 8).toNat = bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat :=
    bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.dw.sub_right (Lay.wSub (by decide))) (by omega)
  have hab := ta.abs a c ⟨hl, hct⟩ (by rw [hH1]; exact ha)
  rw [hD1, hH1] at hab
  -- The counter blocks, as `crypt` takes them.
  have hct3 : CtrS s₃.mem (p.2 2) (ciphOf s₃.mem (p.2 0) (p.2 1).toNat) (inc32 (j0 H iv)) (p.2 6 ++ p.2 5).toNat := by
    rw [hC3, hct]
    have dP' : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [pslotR (p.2 9)],
        (⟨w64 (p.2 2) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
    exact (hcr.congr (blockAt_frame ta.frame (VG.Proof.AesGcm.X86.st_taFrame hc (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame ta.frame (VG.Proof.AesGcm.X86.st_taFrame hc (.inr ⟨by decide, by decide⟩)))).congr
      (blockAt_frame fr (dP' (by decide))) (blockAt_frame fr (dP' (by decide)))
  have hco := co (inc32 (j0 H iv))
  have hct₄ := hco.ctr hct3
  have hout := hco.out hct3
  rw [hC3] at hct₄ hout
  have hD3 : bytesAt s₃.mem (w64 (p.2 7)) (p.2 8).toNat = bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat := by
    rw [bytesAt_frame fr dP (by omega), bytesAt_frame ta.frame (data_taFrame hd.ok) (by omega), hD1]
  rw [hD3] at hout
  have hdrop : (gctr ciph (inc32 (j0 H iv)) (c ++ bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat)).drop c.length =
      xorKs ciph (inc32 (j0 H iv)) c.length (bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat) := by
    rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
  refine ⟨?_, by rw [hout, hdrop, hct]⟩
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit]
  have dP' : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [pslotR (p.2 9)],
      (⟨w64 (p.2 2) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
  refine ⟨?_, ?_, ?_⟩
  · have e₁ := blockAt_frame hco.frame (VG.Proof.AesGcm.X86.st_crFrame hc (d := 0) (k := 16) (by decide))
    have e₂ := blockAt_frame fr (dP' (d := 0) (k := 16) (by decide))
    have e₃ := blockAt_frame ta.frame (VG.Proof.AesGcm.X86.st_taFrame hc (d := 0) (k := 16) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e₁ e₂ e₃
    rw [e₁, e₂, e₃, hj]
  · exact (hab.congr (blockAt_frame fr (dP' (by decide)))
      (bytesAt_frame fr (dP' (d := 32) (k := (Spec.Gcm.ghashInput a _).length % 16) (by omega)) (by omega))).congr
      (blockAt_frame hco.frame (VG.Proof.AesGcm.X86.st_crFrame hc (by decide)))
      (bytesAt_frame hco.frame (VG.Proof.AesGcm.X86.st_crFrame hc (d := 32) (k := (Spec.Gcm.ghashInput a _).length % 16) (by omega))
        (by omega))
  · rw [List.length_append, length_bytesAt, ← hct]; exact hct₄

theorem streamDecrypt_correct (s : State) (hs : streamDecryptX86.pre s) :
    ∃ t s', Exec isa (streamDecrypt vg.callees) s t s' ∧ abiPreserved s s' ∧ streamDecryptX86.post s s' :=
  (VG.Proof.AesGcm.X86.streamDecrypt_pc (pubOf 10 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamDecrypt_ct : ConstantTime isa streamDecryptX86.pre streamDecryptX86.pub (streamDecrypt vg.callees) :=
  Pc.constantTime (pubOf 10) (fun _ _ _ _ h => pubOf_eq h) VG.Proof.AesGcm.X86.streamDecrypt_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Verified`. -/
section

/-!
# AES-GCM on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as an argument
(`Proof/AesGcm/Scratch.lean`): with 28 bytes of stack for the functions that
call `vg_aes_ctr32` (which pushes six arguments, and the return address),
and 24 for `stream_init` and `stream_aad`, which call only `vg_ghash`
(five).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

/-- The CPU features of the functions calling both (here, not in
`Callee.lean`, to keep `List.dedup`'s imports out of the proofs). -/
def GcmImpl.features (v : GcmImpl) : List String := (v.ctr.features ++ v.gh.features).dedup

variable {vg : GcmImpl}

open VG VG.X86 VG.Impl.AesGcm.X86

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition (with no
data): the context at `0x1000`, the state at `0x3000`, the data at `0x2000`
and `scratch` at `0x4000`, as stack arguments at `0x8004`. -/
def saSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30
    else if a = 0x8015 then 0x20 else if a = 0x801d then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 28⟩]

theorem streamAad_verified : Verified X86.target (streamAad vg.callees) (Proof.AesGcm.streamAadScratchContract X86.abi 24) :=
  Verified.of_correct streamAad_correct streamAad_ct (by
    have a0 : arg VG.Proof.AesGcm.X86.saSat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.AesGcm.X86.saSat 1 = 0x3000 := by decide
    have a2 : arg VG.Proof.AesGcm.X86.saSat 2 = 0 := by decide
    have a3 : arg VG.Proof.AesGcm.X86.saSat 3 = 0 := by decide
    have a4 : arg VG.Proof.AesGcm.X86.saSat 4 = 0x2000 := by decide
    have a5 : arg VG.Proof.AesGcm.X86.saSat 5 = 0 := by decide
    have a6 : arg VG.Proof.AesGcm.X86.saSat 6 = 0x4000 := by decide
    have e : argAddr VG.Proof.AesGcm.X86.saSat 0 = 0x8004 := by decide
    have esp : saSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig, Spec.Gcm.streamAadPost, streamAadX86, streamAadPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, e, esp] using VG.Proof.AesGcm.X86.saSat)

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition (with no
nonce): the context at `0x1000`, the nonce at `0x2000`, the state at
`0x3000` and `scratch` at `0x4000`. -/
def siSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20
    else if a = 0x8011 then 0x30 else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 20⟩]

theorem streamInit_verified : Verified X86.target (streamInit vg.callees) (Proof.AesGcm.streamInitScratchContract X86.abi 24) :=
  Verified.of_correct streamInit_correct streamInit_ct (by
    have a0 : arg VG.Proof.AesGcm.X86.siSat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.AesGcm.X86.siSat 1 = 0x2000 := by decide
    have a2 : arg VG.Proof.AesGcm.X86.siSat 2 = 0 := by decide
    have a3 : arg VG.Proof.AesGcm.X86.siSat 3 = 0x3000 := by decide
    have a4 : arg VG.Proof.AesGcm.X86.siSat 4 = 0x4000 := by decide
    have e : argAddr VG.Proof.AesGcm.X86.siSat 0 = 0x8004 := by decide
    have esp : siSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig, Spec.Gcm.streamInitPost, streamInitX86, streamInitPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, e, esp] using VG.Proof.AesGcm.X86.siSat)

/-- A state satisfying the precondition of `vg_aes_gcm_stream_encrypt` and
`_decrypt` (with no data): the context at `0x1000`, 10 rounds, the state at
`0x3000`, the data at `0x2000` and `scratch` at `0x4000`. -/
def crSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x30
    else if a = 0x8021 then 0x20 else if a = 0x8029 then 0x40 else 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 40⟩]

theorem streamEncrypt_verified : Verified X86.target (streamEncrypt vg.callees) (Proof.AesGcm.streamEncryptScratchContract X86.abi 28) :=
  Verified.of_correct VG.Proof.AesGcm.X86.streamEncrypt_correct VG.Proof.AesGcm.X86.streamEncrypt_ct (by
    have a0 : arg VG.Proof.AesGcm.X86.crSat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.AesGcm.X86.crSat 1 = 10 := by decide
    have a2 : arg VG.Proof.AesGcm.X86.crSat 2 = 0x3000 := by decide
    have a3 : arg VG.Proof.AesGcm.X86.crSat 3 = 0 := by decide
    have a4 : arg VG.Proof.AesGcm.X86.crSat 4 = 0 := by decide
    have a5 : arg VG.Proof.AesGcm.X86.crSat 5 = 0 := by decide
    have a6 : arg VG.Proof.AesGcm.X86.crSat 6 = 0 := by decide
    have a7 : arg VG.Proof.AesGcm.X86.crSat 7 = 0x2000 := by decide
    have a8 : arg VG.Proof.AesGcm.X86.crSat 8 = 0 := by decide
    have a9 : arg VG.Proof.AesGcm.X86.crSat 9 = 0x4000 := by decide
    have e : argAddr VG.Proof.AesGcm.X86.crSat 0 = 0x8004 := by decide
    have esp : crSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, Spec.Gcm.streamDecryptPost, streamEncryptX86, streamCryptPre, pubN,
      roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp] using VG.Proof.AesGcm.X86.crSat)

theorem streamDecrypt_verified : Verified X86.target (streamDecrypt vg.callees) (Proof.AesGcm.streamDecryptScratchContract X86.abi 28) :=
  Verified.of_correct VG.Proof.AesGcm.X86.streamDecrypt_correct VG.Proof.AesGcm.X86.streamDecrypt_ct (by
    have a0 : arg VG.Proof.AesGcm.X86.crSat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.AesGcm.X86.crSat 1 = 10 := by decide
    have a2 : arg VG.Proof.AesGcm.X86.crSat 2 = 0x3000 := by decide
    have a3 : arg VG.Proof.AesGcm.X86.crSat 3 = 0 := by decide
    have a4 : arg VG.Proof.AesGcm.X86.crSat 4 = 0 := by decide
    have a5 : arg VG.Proof.AesGcm.X86.crSat 5 = 0 := by decide
    have a6 : arg VG.Proof.AesGcm.X86.crSat 6 = 0 := by decide
    have a7 : arg VG.Proof.AesGcm.X86.crSat 7 = 0x2000 := by decide
    have a8 : arg VG.Proof.AesGcm.X86.crSat 8 = 0 := by decide
    have a9 : arg VG.Proof.AesGcm.X86.crSat 9 = 0x4000 := by decide
    have e : argAddr VG.Proof.AesGcm.X86.crSat 0 = 0x8004 := by decide
    have esp : crSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, Spec.Gcm.streamDecryptPost, streamDecryptX86, streamCryptPre, pubN,
      roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp] using VG.Proof.AesGcm.X86.crSat)

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition: the
context at `0x1000`, 10 rounds, the state at `0x3000`, the tag at `0x5000`
and `work` at `0x4000`. -/
def finSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x30
    else if a = 0x8021 then 0x50 else if a = 0x8025 then 0x40 else 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 36⟩]

theorem streamFinish_verified :
    Verified X86.target (streamFinish vg.callees) (Proof.AesGcm.streamFinishScratchContract X86.abi 28) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    have a0 : arg VG.Proof.AesGcm.X86.finSat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.AesGcm.X86.finSat 1 = 10 := by decide
    have a2 : arg VG.Proof.AesGcm.X86.finSat 2 = 0x3000 := by decide
    have a3 : arg VG.Proof.AesGcm.X86.finSat 3 = 0 := by decide
    have a4 : arg VG.Proof.AesGcm.X86.finSat 4 = 0 := by decide
    have a5 : arg VG.Proof.AesGcm.X86.finSat 5 = 0 := by decide
    have a6 : arg VG.Proof.AesGcm.X86.finSat 6 = 0 := by decide
    have a7 : arg VG.Proof.AesGcm.X86.finSat 7 = 0x5000 := by decide
    have a8 : arg VG.Proof.AesGcm.X86.finSat 8 = 0x4000 := by decide
    have e : argAddr VG.Proof.AesGcm.X86.finSat 0 = 0x8004 := by decide
    have esp : finSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Spec.Gcm.streamFinishPost, streamFinishX86, finPre, pubN,
      roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using VG.Proof.AesGcm.X86.finSat)

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition: as
`finSat`, with a received tag of no bytes at `0x5000`. -/
def verSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x30
    else if a = 0x8021 then 0x50 else if a = 0x8029 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 40⟩]

theorem streamVerify_verified :
    Verified X86.target (streamVerify vg.callees) (Proof.AesGcm.streamVerifyScratchContract X86.abi 28) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    have a0 : arg VG.Proof.AesGcm.X86.verSat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.AesGcm.X86.verSat 1 = 10 := by decide
    have a2 : arg VG.Proof.AesGcm.X86.verSat 2 = 0x3000 := by decide
    have a3 : arg VG.Proof.AesGcm.X86.verSat 3 = 0 := by decide
    have a4 : arg VG.Proof.AesGcm.X86.verSat 4 = 0 := by decide
    have a5 : arg VG.Proof.AesGcm.X86.verSat 5 = 0 := by decide
    have a6 : arg VG.Proof.AesGcm.X86.verSat 6 = 0 := by decide
    have a7 : arg VG.Proof.AesGcm.X86.verSat 7 = 0x5000 := by decide
    have a8 : arg VG.Proof.AesGcm.X86.verSat 8 = 0 := by decide
    have a9 : arg VG.Proof.AesGcm.X86.verSat 9 = 0x4000 := by decide
    have e : argAddr VG.Proof.AesGcm.X86.verSat 0 = 0x8004 := by decide
    have esp : verSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
      Spec.Gcm.streamVerifyPre, Spec.Gcm.streamVerifyPost, streamVerifyX86, verifyPre, pubN,
      roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp] using VG.Proof.AesGcm.X86.verSat)

/-- A state satisfying `vg_aes_gcm_seal`'s precondition (with no nonce,
additional data or data): the context at `0x1000`, 10 rounds, the nonce at
`0x2000`, the additional data at `0x2100`, the data at `0x3000`, the tag at
`0x5000` and `work` at `0x4000`. -/
def sealSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8015 then 0x21 else if a = 0x801d then 0x30 else if a = 0x8025 then 0x50
    else if a = 0x8029 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 40⟩]

theorem seal_verified : Verified X86.target («seal» vg.callees) (Proof.AesGcm.sealScratchContract X86.abi 28) :=
  Verified.of_correct VG.Proof.AesGcm.X86.seal_correct VG.Proof.AesGcm.X86.seal_ct (by
    have a0 : arg VG.Proof.AesGcm.X86.sealSat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.AesGcm.X86.sealSat 1 = 10 := by decide
    have a2 : arg VG.Proof.AesGcm.X86.sealSat 2 = 0x2000 := by decide
    have a3 : arg VG.Proof.AesGcm.X86.sealSat 3 = 0 := by decide
    have a4 : arg VG.Proof.AesGcm.X86.sealSat 4 = 0x2100 := by decide
    have a5 : arg VG.Proof.AesGcm.X86.sealSat 5 = 0 := by decide
    have a6 : arg VG.Proof.AesGcm.X86.sealSat 6 = 0x3000 := by decide
    have a7 : arg VG.Proof.AesGcm.X86.sealSat 7 = 0 := by decide
    have a8 : arg VG.Proof.AesGcm.X86.sealSat 8 = 0x5000 := by decide
    have a9 : arg VG.Proof.AesGcm.X86.sealSat 9 = 0x4000 := by decide
    have e : argAddr VG.Proof.AesGcm.X86.sealSat 0 = 0x8004 := by decide
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Spec.Gcm.sealPost, sealX86, sealPre, pubN, roundsOk,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp] using VG.Proof.AesGcm.X86.sealSat)

/-- A state satisfying `vg_aes_gcm_open`'s precondition: as `sealSat`, with
a received tag of no bytes at `0x5000`. -/
def openSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8015 then 0x21 else if a = 0x801d then 0x30 else if a = 0x8025 then 0x50
    else if a = 0x802d then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 44⟩]

/-- The leak `open` may have, for valid `rounds`: whether it succeeds. -/
theorem leak_bool {P Q : Prop} [Decidable P] [Decidable Q] {a b : Bool} (hP : P) (hQ : Q)
    (h : (if ¬P then ([] : List Nat) else [if a = true then 1 else 0]) =
      (if ¬Q then [] else [if b = true then 1 else 0])) : a = b := by
  simp only [hP, hQ, not_true_eq_false, ↓reduceIte, List.cons.injEq, and_true] at h
  cases a <;> cases b <;> simp_all

theorem openPre_rounds {s : State} (h : openPre s) : roundsOk s 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, h⟩ := h
  exact h

theorem open_pre : ∀ s, (Proof.AesGcm.openScratchContract X86.abi 28).pre s → openX86.pre s := by
  sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
    Spec.Gcm.openPost, Spec.Gcm.openLeak, openX86, openPre, pubN, roundsOk,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds (`rounds` being valid). -/
theorem open_verified : Verified X86.target («open» vg.callees) (Proof.AesGcm.openScratchContract X86.abi 28) :=
  Verified.of_correct VG.Proof.AesGcm.X86.open_correct VG.Proof.AesGcm.X86.open_ct
    { pre := VG.Proof.AesGcm.X86.open_pre
      post := by sig_implies_post [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig,
        Spec.Gcm.openPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, openX86, openPre, pubN, roundsOk,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by
        intro s₁ s₂ h₁ h₂ h
        have hR₁ := VG.Proof.AesGcm.X86.openPre_rounds (VG.Proof.AesGcm.X86.open_pre s₁ h₁)
        have hR₂ := VG.Proof.AesGcm.X86.openPre_rounds (VG.Proof.AesGcm.X86.open_pre s₂ h₂)
        sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          Spec.Gcm.openPost, Spec.Gcm.openLeak, openX86, openPre, pubN, roundsOk,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
        sig_split h
        sig_reduce [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          Spec.Gcm.openPost, Spec.Gcm.openLeak, openX86, openPre, pubN, roundsOk,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        sig_simp [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          Spec.Gcm.openPost, Spec.Gcm.openLeak, openX86, openPre, pubN, roundsOk,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [Nat.forall_lt_succ_right, Nat.not_lt_zero,
          false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | (apply VG.Proof.AesGcm.X86.leak_bool hR₁ hR₂; with_reducible assumption)
      sat := by
        have a0 : arg VG.Proof.AesGcm.X86.openSat 0 = 0x1000 := by decide
        have a1 : arg VG.Proof.AesGcm.X86.openSat 1 = 10 := by decide
        have a2 : arg VG.Proof.AesGcm.X86.openSat 2 = 0x2000 := by decide
        have a3 : arg VG.Proof.AesGcm.X86.openSat 3 = 0 := by decide
        have a4 : arg VG.Proof.AesGcm.X86.openSat 4 = 0x2100 := by decide
        have a5 : arg VG.Proof.AesGcm.X86.openSat 5 = 0 := by decide
        have a6 : arg VG.Proof.AesGcm.X86.openSat 6 = 0x3000 := by decide
        have a7 : arg VG.Proof.AesGcm.X86.openSat 7 = 0 := by decide
        have a8 : arg VG.Proof.AesGcm.X86.openSat 8 = 0x5000 := by decide
        have a9 : arg VG.Proof.AesGcm.X86.openSat 9 = 0 := by decide
        have a10 : arg VG.Proof.AesGcm.X86.openSat 10 = 0x4000 := by decide
        have e : argAddr VG.Proof.AesGcm.X86.openSat 0 = 0x8004 := by decide
        have esp : openSat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          Spec.Gcm.openPost, Spec.Gcm.openLeak, openX86, openPre, pubN, roundsOk,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using VG.Proof.AesGcm.X86.openSat }

/-- A state satisfying `vg_aes_gcm_init`'s precondition: a 16-byte key at
`0x1000`, the context at `0x2000` and `scratch` at `0x4000`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 16⟩]

theorem init_verified : Verified X86.target (init vg.callees) (Proof.AesGcm.initScratchContract X86.abi 28) :=
  Verified.of_correct init_correct init_ct (by
    have a0 : arg VG.Proof.AesGcm.X86.initSat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.AesGcm.X86.initSat 1 = 16 := by decide
    have a2 : arg VG.Proof.AesGcm.X86.initSat 2 = 0x2000 := by decide
    have a3 : arg VG.Proof.AesGcm.X86.initSat 3 = 0x4000 := by decide
    have e : argAddr VG.Proof.AesGcm.X86.initSat 0 = 0x8004 := by decide
    have esp : initSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre, Spec.Gcm.initPost, initX86, initPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, e, esp] using VG.Proof.AesGcm.X86.initSat)


/-! ## The stack pointer -/

section
variable (vg : GcmImpl)

theorem init_spSafe : (init vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, tagOut, «open», «seal», Code.all, GcmImpl.callees, vg.ctr.spSafe, vg.ctr.expandSpSafe, vg.gh.spSafe,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamInit_spSafe : (streamInit vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, tagOut, «open», «seal», Code.all, GcmImpl.callees, vg.ctr.spSafe, vg.ctr.expandSpSafe, vg.gh.spSafe,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamAad_spSafe : (streamAad vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, tagOut, «open», «seal», Code.all, GcmImpl.callees, vg.ctr.spSafe, vg.ctr.expandSpSafe, vg.gh.spSafe,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamEncrypt_spSafe : (streamEncrypt vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, tagOut, «open», «seal», Code.all, GcmImpl.callees, vg.ctr.spSafe, vg.ctr.expandSpSafe, vg.gh.spSafe,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamDecrypt_spSafe : (streamDecrypt vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, tagOut, «open», «seal», Code.all, GcmImpl.callees, vg.ctr.spSafe, vg.ctr.expandSpSafe, vg.gh.spSafe,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamFinish_spSafe : (streamFinish vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, tagOut, «open», «seal», Code.all, GcmImpl.callees, vg.ctr.spSafe, vg.ctr.expandSpSafe, vg.gh.spSafe,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamVerify_spSafe : (streamVerify vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, tagOut, «open», «seal», Code.all, GcmImpl.callees, vg.ctr.spSafe, vg.ctr.expandSpSafe, vg.gh.spSafe,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_spSafe : («seal» vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, tagOut, «open», «seal», Code.all, GcmImpl.callees, vg.ctr.spSafe, vg.ctr.expandSpSafe, vg.gh.spSafe,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem open_spSafe : («open» vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush, ghCall, ghash1, init, j0, j0hash, keyCall, lens, oneAad, oneCrypt, oneTag, streamAad, streamDecrypt, streamEncrypt, streamFinish, streamInit, streamVerify, tag, textAbsorb, tagOut, «open», «seal», Code.all, GcmImpl.callees, vg.ctr.spSafe, vg.ctr.expandSpSafe, vg.gh.spSafe,
    Bool.true_and, Bool.and_true]
  decide +kernel

end

end VG.Proof.AesGcm.X86

end
