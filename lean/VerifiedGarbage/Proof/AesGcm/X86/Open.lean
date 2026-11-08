module
public import VerifiedGarbage.Proof.AesGcm.X86.OneTag

import VerifiedGarbage.Proof.AesGcm.X86.Seal
import VerifiedGarbage.Proof.AesGcm.X86.OneAad
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86.OneTag
meta import VerifiedGarbage.Proof.AesGcm.X86.Seal
meta import VerifiedGarbage.Proof.AesGcm.X86.OneAad
meta import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

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

@[expose] public section

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
    openRes s₀ = oRes p s₀ := by
  simp only [openRes, oRes, open_arg hp (i := 0) (by decide), open_arg hp (i := 1) (by decide),
    open_arg hp (i := 2) (by decide), open_arg hp (i := 3) (by decide), open_arg hp (i := 4) (by decide),
    open_arg hp (i := 5) (by decide), open_arg hp (i := 6) (by decide), open_arg hp (i := 7) (by decide),
    open_tag hp, open_arg hp (i := 9) (by decide)]

/-- The tag of the message, and the tag received. -/
abbrev tagOf (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : List Byte :=
  fullTag (ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat) (ctxH s₀.mem (w64 (p.2 0)))
    (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat) (bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat)
    (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat)

abbrev rcvOf (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : List Byte :=
  bytesAt s₀.mem (w64 (p.2 10)) (p.2 9).toNat

theorem oRes_ok {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (ht : Spec.Gcm.tagLenOk (p.2 9).toNat = true) :
    oRes p s₀ = if (tagOf p s₀).take (p.2 9).toNat = rcvOf p s₀ then
      some (gctr (ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat) (inc32 (jOf p s₀))
        (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat)) else none := by
  simp only [oRes, openResult, ht, ↓reduceIte, decryptWith]

theorem oRes_bad {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (ht : Spec.Gcm.tagLenOk (p.2 9).toNat = false) :
    oRes p s₀ = none := by
  simp only [oRes, openResult, ht, Bool.false_eq_true, ↓reduceIte]

/-- The public data of a run of the body: its arguments (`W` at 8, `tag` at
10), a word more (`dst`, out of place), and whether the tag is right. -/
abbrev OQ : Type := ((BitVec 32 × (Nat → BitVec 32)) × BitVec 32) × Bool

/-- What is fixed of a run of `open`'s body for the index `q`, entered in a
state satisfying `Pre`, the word more `x`. -/
structure IX (Pre : State → Prop) (x : State → BitVec 32) (q : OQ) (s₀ : State) : Prop where
  pre : Pre s₀
  pub : pubSw 11 8 s₀ = q.1.1
  ext : x s₀ = q.1.2
  res : (oRes q.1.1 s₀).isSome = q.2

theorem IX.q2 {Pre : State → Prop} {x : State → BitVec 32} {q : OQ} {s₀ : State} (h : IX Pre x q s₀)
    (ht : Spec.Gcm.tagLenOk (q.1.1.2 9).toNat = true) :
    q.2 = decide ((tagOf q.1.1 s₀).take (q.1.1.2 9).toNat = rcvOf q.1.1 s₀) := by
  rw [← h.res, oRes_ok ht]
  split <;> simp_all

/-- What the body returns, before the exit: the bytes `out` the result is in
(the data in place, `dst` out of place) are the plaintext if the tag is right,
and `fb` (the data as they were, or zeros) if not. -/
def PostO (out : BitVec 32 × (Nat → BitVec 32) → BitVec 32 → State → List Byte)
    (fb : BitVec 32 × (Nat → BitVec 32) → State → List Byte) (p : BitVec 32 × (Nat → BitVec 32))
    (x : BitVec 32) (s₀ s : State) : Prop :=
  match oRes p s₀ with
  | some pt => s.gpr .eax = 1 ∧ out p x s = pt
  | none => s.gpr .eax = 0 ∧ out p x s = fb p s₀

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
  · exact slot_oF G h₁ h₂ r (List.mem_cons_of_mem _ hr)

omit G in
/-- A region apart from `W` and the stack the calls use, apart from what the pieces write. -/
theorem t_woF {o : Nat} (ho : o + 16 ≤ 2560) {T : Region} (tw : T.Disjoint ⟨w64 (p.2 8), 2560⟩)
    (kt : (below p.1 32).Disjoint T) : ∀ r ∈ ⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: oF p, T.Disjoint r := by
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

section
variable (Pre : State → Prop) (x : State → BitVec 32)

/-- After the received tag is compared and the result kept at `W + auxO`. -/
structure OC (q : OQ) (s₀ s : State) : Prop where
  o : OEnv q.1.1 s₀ s
  ix : IX Pre x q s₀
  aux : slotv s.mem (q.1.1.2 8) auxO = BitVec.ofNat 32 (if q.2 = true then 1 else 0)
  zf : s.zf = some (!q.2)
  cb : blockAt s.mem (w64 (stOf (q.1.1.2 8)) + BitVec.ofNat 64 48) = inc32 (jOf q.1.1 s₀)
  data : bytesAt s.mem (w64 (q.1.1.2 6)) (q.1.1.2 7).toNat = bytesAt s₀.mem (w64 (q.1.1.2 6)) (q.1.1.2 7).toNat

/-- After the data is decrypted if the tag is right: the result in `out`,
`fb` if the tag is wrong. -/
structure OD (out : BitVec 32 × (Nat → BitVec 32) → BitVec 32 → State → List Byte)
    (fb : BitVec 32 × (Nat → BitVec 32) → State → List Byte) (q : OQ) (s₀ s : State) : Prop where
  o : OEnv q.1.1 s₀ s
  ix : IX Pre x q s₀
  aux : slotv s.mem (q.1.1.2 8) auxO = BitVec.ofNat 32 (if q.2 = true then 1 else 0)
  out : out q.1.1 q.1.2 s = if q.2 = true then
    gctr (ctxCiph s₀.mem (w64 (q.1.1.2 0)) (q.1.1.2 1).toNat) (inc32 (jOf q.1.1 s₀))
      (bytesAt s₀.mem (w64 (q.1.1.2 6)) (q.1.1.2 7).toNat) else fb q.1.1 s₀

end

/-- A run of `open`'s body: entered in a state satisfying `Pre`, which has
`open`'s arguments (`op`, `tg`), with `x` public too, the result in `out`
(`fb` if the tag is wrong), and what it runs if the tag length is not one
`tagLenOk` allows (`bad`, with `eax := 0`), if the tag is wrong (`fail`) and if
it is right (`dec`). -/
structure OMode (vg : GcmImpl) where
  Pre : State → Prop
  op : ∀ s, Pre s → OP 11 10 s
  tg : ∀ s, Pre s → Covers [⟨w64 (arg s 8), (arg s 9).toNat⟩] (s.rd ++ s.wr) ∧
    (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧
    (⟨w64 (arg s 8), (arg s 9).toNat⟩ : Region).Disjoint ⟨w64 (arg s 10), 2560⟩ ∧
    (below (s.gpr .esp) 32).Disjoint ⟨w64 (arg s 8), (arg s 9).toNat⟩
  x : State → BitVec 32
  out : BitVec 32 × (Nat → BitVec 32) → BitVec 32 → State → List Byte
  fb : BitVec 32 × (Nat → BitVec 32) → State → List Byte
  out_mem : ∀ p y {s s' : State}, s'.mem = s.mem → out p y s' = out p y s
  bad : Prog isa
  fail : Prog isa
  dec : Prog isa
  hbad : ∀ q : OQ, Spec.Gcm.tagLenOk (q.1.1.2 9).toNat = false →
    Pc (fun s₀ s => OEnt q.1.1 s₀ s ∧ slotv s.mem (q.1.1.2 8) tglO = BitVec.ofNat 32 (q.1.1.2 9).toNat ∧
        IX Pre x q s₀ ∧ s.zf = some true) bad
      (fun s₀ s => OEnv q.1.1 s₀ s ∧ IX Pre x q s₀ ∧ s.gpr .eax = 0 ∧ out q.1.1 q.1.2 s = fb q.1.1 s₀)
  hfail : ∀ q : OQ, q.2 = false → Pc (OC Pre x q) fail (OD Pre x out fb q)
  hdec : ∀ q : OQ, q.2 = true → Pc (OC Pre x q) dec (OD Pre x out fb q)

theorem openBody_eq (bad fail dec : Prog isa) : (openBody vg.callees bad fail dec) =
    .seq (oneEntry 10 ([(8, tpO), (9, tglO)].flatMap
    (fun (p : Nat × Nat) => keep p.1 p.2))) (.seq tagLenOk (.seq (.ite .e bad
    (.seq (oneAad vg.callees) (.seq (oneTag vg.callees uO) (.seq recv (.seq (cmp uO)
      (.seq (.block [.store (at_ .ebp auxO) .eax, .alu .test .eax (.reg .eax)])
      (.seq (.ite .e fail dec) (.block [.mov .eax (slot auxO)]))))))))
    (.block restore))) := rfl

/-- `open`'s body, in any mode, from its entry to its exit. -/
theorem openBody_pc (M : OMode vg) (q : OQ) :
    Pc (fun (s₀ : State) s => M.Pre s₀ ∧ ((pubSw 11 8 s₀, M.x s₀), (openRes s₀).isSome) = q ∧ s = s₀)
      (openBody vg.callees M.bad M.fail M.dec)
      (fun s₀ s' => abiPreserved s₀ s' ∧ IX M.Pre M.x q s₀ ∧ PostO M.out M.fb q.1.1 q.1.2 s₀ s') := by
  by_cases hex : ∃ s₀, M.Pre s₀ ∧ ((pubSw 11 8 s₀, M.x s₀), (openRes s₀).isSome) = q
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzq⟩ := hex
  have hzp : pubSw 11 8 z = q.1.1 := by rw [← hzq]
  have G : OL q.1.1 := (M.op _ hz).ol rfl (by decide) hzp
  have L := G.L
  obtain ⟨-, ftg, tw, kt⟩ := M.tg _ hz
  rw [open_tag hzp, open_arg hzp (i := 9) (by decide)] at ftg
  rw [open_tag hzp, open_arg hzp (i := 9) (by decide), pubSw_W hzp (m := 10) (by decide) rfl] at tw
  rw [open_tag hzp, open_arg hzp (i := 9) (by decide), pubSw_esp hzp] at kt
  have ht32 : (q.1.1.2 9).toNat < 2 ^ 32 := (q.1.1.2 9).isLt
  generalize hok : Spec.Gcm.tagLenOk (q.1.1.2 9).toNat = ok
  rw [openBody_eq]
  -- The entry.
  refine Pc.seq (Pc.mono (oneEntry_pc 11 10 rfl (by decide) [(8, tpO), (9, tglO)] (by decide) (by decide) (by simp)
    (fun s₀ => M.Pre s₀ ∧ M.x s₀ = q.1.2 ∧ (openRes s₀).isSome = q.2) (fun _ h => M.op _ h.1) q.1.1 G
    (by native_taint_decide) (by native_taint_decide))
    (fun s₀ s ⟨h₁, hq, hs⟩ => ⟨⟨h₁, by rw [← hq], by rw [← hq]⟩, by rw [← hq], hs⟩) (fun _ _ h => h)) ?_
  -- The tag length.
  refine Pc.seq (Q := fun s₀ s => OEnt q.1.1 s₀ s ∧
      slotv s.mem (q.1.1.2 8) tglO = BitVec.ofNat 32 (q.1.1.2 9).toNat ∧ IX M.Pre M.x q s₀ ∧ s.zf = some (!ok))
    (Pc.mono (Pc.lift (tagLenOk_pc (W := q.1.1.2 8) ht32) (fun _ s => s) fun s₀ s ⟨h, ht, hp, _⟩ =>
      ⟨rfl, h.o.env.ebp, L.aW (by decide), h.o.env.wIn' (by decide), by
        rw [ht (9, tglO) (by simp), open_arg hp (i := 9) (by decide), ofNat_toNat32]⟩) (fun _ _ h => h)
      fun s₀ s ⟨s₁, ⟨h, ht, hp, hpre, hxe, hres⟩, ⟨tl, hzf⟩, _, _⟩ =>
        ⟨h.same G tl.mem (tl.other _ (by decide) (by decide)) (tl.other _ (by decide) (by decide))
          (tl.other _ (by decide) (by decide)) tl.rd tl.wr,
          by rw [tl.mem, ht (9, tglO) (by simp), open_arg hp (i := 9) (by decide), ofNat_toNat32],
          ⟨hpre, hp, hxe, by rw [← openRes_eq hp]; exact hres⟩, by rw [hzf, hok]⟩) ?_
  refine Pc.seq (Q := fun s₀ s => OEnv q.1.1 s₀ s ∧ IX M.Pre M.x q s₀ ∧ PostO M.out M.fb q.1.1 q.1.2 s₀ s)
    (Pc.ite (!ok) (fun _ _ h => h.2.2.2) (fun hb => ?_) (fun hb => ?_)) ?_
  -- A tag length `tagLenOk` does not allow.
  · have hf : ok = false := by simpa using hb
    have hF : Spec.Gcm.tagLenOk (q.1.1.2 9).toNat = false := by rw [hok, hf]
    refine Pc.mono (M.hbad q hF) (fun s₀ s ⟨h, ht, hx, hz⟩ => ⟨h, ht, hx, by rw [hz, hf]; rfl⟩)
      fun s₀ s ⟨o, hx, ha, hout⟩ => ⟨o, hx, ?_⟩
    simp only [PostO, oRes_bad hF]
    exact ⟨ha, hout⟩
  -- An allowed one.
  have hT : ok = true := by simpa using hb
  have hT' : Spec.Gcm.tagLenOk (q.1.1.2 9).toNat = true := by rw [hok, hT]
  have ht' : 1 ≤ (q.1.1.2 9).toNat ∧ (q.1.1.2 9).toNat ≤ 16 := by
    have := hT'
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at this
    omega
  obtain ⟨t1, t16⟩ := ht'
  -- `J₀` and the additional data; the tag of the ciphertext.
  refine Pc.seq (Pc.lift (oneAad_pc G) (fun s₀ s => (s₀, s)) fun s₀ s h => ⟨h.1, rfl⟩) ?_
  refine Pc.seq (Pc.lift (oneTag_pc G (o := 112) (.inr rfl)) (fun s₀ s => (s₀, s))
    fun s₀ s ⟨_, _, ⟨ha, _⟩, _⟩ => ⟨⟨ha.o, ha.j, ha.y⟩, rfl⟩) ?_
  -- The received tag copied.
  have tgl : ∀ {sA s₂ s₃ : State}, slotv sA.mem (q.1.1.2 8) tglO = BitVec.ofNat 32 (q.1.1.2 9).toNat →
      Frame (oF q.1.1) sA.mem s₂.mem → Frame (oT q.1.1 112) s₂.mem s₃.mem →
      slotv s₃.mem (q.1.1.2 8) tglO = BitVec.ofNat 32 (q.1.1.2 9).toNat := fun hs fA fT => by
    rw [slotv_eq, slot_frame (oT_oF fT) (kept_woF G (o := tglO) (by decide) (.inl (by decide)) (by decide)),
      slot_frame fA fun r hr => slot_oF G (o := tglO) (by decide) (.inl (by decide)) r
        (List.mem_cons_of_mem _ hr), ← slotv_eq]
    exact hs
  refine Pc.seq (Pc.of (I := fun s => WEnv (q.1.1.2 8) s ∧
      slotv s.mem (q.1.1.2 8) tglO = BitVec.ofNat 32 (q.1.1.2 9).toNat ∧ slotv s.mem (q.1.1.2 8) tpO = q.1.1.2 10 ∧
      Covers [⟨w64 (q.1.1.2 10), (q.1.1.2 9).toNat⟩] (s.rd ++ s.wr))
    (R := fun s s' => bytesAt s'.mem (w64 (q.1.1.2 8) + BitVec.ofNat 64 rO) 16 =
        bytesAt s.mem (w64 (q.1.1.2 10)) (q.1.1.2 9).toNat ++ zeros (16 - (q.1.1.2 9).toNat) ∧
      Frame [⟨w64 (q.1.1.2 8) + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (fun s hs => recv_ok hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 ftg tw t1 t16)
    (recv_ct fun s hs => ⟨hs.1, hs.2.1, hs.2.2.1⟩) _
    (fun s₀ s₃ ⟨s₂, ⟨sA, ⟨_, hs, hx, _⟩, ⟨_, fA⟩, _⟩, ⟨o₃, _, fT⟩, _⟩ =>
      ⟨⟨o₃.env.ebp, o₃.env.wW, L.fw⟩, tgl hs fA fT, by rw [o₃.tp, open_tag hx.pub], by
        rw [o₃.rd, o₃.wr, ← open_tag hx.pub, ← open_arg hx.pub (i := 9) (by decide)]
        exact (M.tg _ hx.pre).1⟩)) ?_
  -- Compared.
  have rR_tgl : ∀ {s s' : State}, Frame [⟨w64 (q.1.1.2 8) + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem →
      slotv s'.mem (q.1.1.2 8) tglO = slotv s.mem (q.1.1.2 8) tglO := fun f => by
    rw [slotv_eq, slotv_eq]
    exact slot_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine Pc.seq (Pc.of (I := fun s => WEnv (q.1.1.2 8) s ∧
      slotv s.mem (q.1.1.2 8) tglO = BitVec.ofNat 32 (q.1.1.2 9).toNat)
    (R := fun s s' => s'.gpr .eax = BitVec.ofNat 32
        (if bytesAt s.mem (w64 (q.1.1.2 8) + BitVec.ofNat 64 uO) (q.1.1.2 9).toNat ++ zeros (16 - (q.1.1.2 9).toNat) =
            bytesAt s.mem (w64 (q.1.1.2 8) + BitVec.ofNat 64 rO) 16 then 1 else 0) ∧
      Frame [⟨w64 (q.1.1.2 8) + BitVec.ofNat 64 vO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (fun s hs => cmp_ok hs.1 hs.2 t1 t16 (by decide)) (cmp_ct (.inr rfl) fun s hs => hs) _
    (fun s₀ s₄ ⟨s₃, ⟨s₂, ⟨sA, ⟨_, hs, _⟩, ⟨_, fA⟩, _⟩, ⟨o₃, _, fT⟩, _⟩, ⟨_, f₄, bp₄, _, _, _, wr₄⟩⟩ =>
      ⟨⟨by rw [bp₄, o₃.env.ebp], by rw [wr₄]; exact o₃.env.wW, L.fw⟩, by rw [rR_tgl f₄]; exact tgl hs fA fT⟩)) ?_
  -- The result kept, and tested.
  refine Pc.seq (Q := OC M.Pre M.x q) (Pc.taint [.ebp] (fun s₀ s₅ hk => ?_)
    (fun _ _ s₁ s₂ ⟨_, ⟨_, ⟨_, _, ⟨o₁, _⟩, _⟩, _, _, e₁, _⟩, _, _, e₁', _⟩
      ⟨_, ⟨_, ⟨_, _, ⟨o₂, _⟩, _⟩, _, _, e₂, _⟩, _, _, e₂', _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁', e₁, e₂', e₂, o₁.env.ebp, o₂.env.ebp])
    (by native_taint_decide)) ?_
  · obtain ⟨s₄, ⟨s₃, ⟨s₂, ⟨sA, ⟨hE, _, hx, _⟩, ⟨ha, fA⟩, _⟩, ⟨o₃, ht, fT⟩, _⟩,
      ⟨b₄, f₄, bp₄, si₄, sp₄, rd₄, wr₄⟩⟩, ⟨a₅, f₅, bp₅, si₅, sp₅, rd₅, wr₅⟩⟩ := hk
    have fo₄ : Frame (oF q.1.1) s₃.mem s₄.mem := f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    have fo₅ : Frame (oF q.1.1) s₄.mem s₅.mem := f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wsR (q.1.1.2 8), by simp, Offset.sub _ (by decide) (by decide)⟩
    have o₅ := (o₃.frame G (Frame.oD fo₄) bp₄ si₄ sp₄ rd₄ wr₄).frame G (Frame.oD fo₅) bp₅ si₅ sp₅ rd₅ wr₅
    -- The tags.
    have hc₂ : bytesAt s₂.mem (w64 (q.1.1.2 6)) (q.1.1.2 7).toNat = bytesAt s₀.mem (w64 (q.1.1.2 6)) (q.1.1.2 7).toNat := by
      rw [bytesAt_frame fA (d_oF G) (by have := G.fd; omega)]; exact hE.data
    have hT₃ : bytesAt s₃.mem (w64 (q.1.1.2 8) + BitVec.ofNat 64 uO) 16 = tagOf q.1.1 s₀ := by
      dsimp only at ht
      rw [ht, hc₂, tagOf, Proof.Gcm.fullTag_eq, padded_eq, length_bytesAt, length_bytesAt]
    have hT₄ : bytesAt s₄.mem (w64 (q.1.1.2 8) + BitVec.ofNat 64 uO) (q.1.1.2 9).toNat =
        (tagOf q.1.1 s₀).take (q.1.1.2 9).toNat := by
      rw [← bytesAt_take _ _ t16, bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), hT₃]
    have hw₃ : bytesAt s₃.mem (w64 (q.1.1.2 10)) (q.1.1.2 9).toNat = rcvOf q.1.1 s₀ := by
      have ht₁ : (q.1.1.2 9).toNat ≤ 2 ^ 64 := by omega
      rw [bytesAt_frame (oT_oF fT) (t_woF (by decide) tw kt) ht₁,
        bytesAt_frame fA (fun r hr => t_woF (o := 0) (by decide) tw kt r (List.mem_cons_of_mem _ hr)) ht₁,
        bytesAt_frame hE.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact tw.sub_right (Lay.wSub (by decide))) ht₁]
    have hR₄ : bytesAt s₄.mem (w64 (q.1.1.2 8) + BitVec.ofNat 64 rO) 16 =
        rcvOf q.1.1 s₀ ++ zeros (16 - (q.1.1.2 9).toNat) := by
      rw [b₄, hw₃]
    have hq2 := hx.q2 hT'
    have a₅' : s₅.gpr .eax = BitVec.ofNat 32 (if q.2 = true then 1 else 0) := by
      rw [a₅, hT₄, hR₄, hq2]
      by_cases h : (tagOf q.1.1 s₀).take (q.1.1.2 9).toNat = rcvOf q.1.1 s₀
      · simp only [h, List.append_left_inj, decide_true, ↓reduceIte]
      · simp only [h, List.append_left_inj, decide_false, Bool.false_eq_true, ↓reduceIte]
    have aW := o₅.env.wIn (d := auxO) (n := 4) (by decide)
    refine WP.of_runBlock ⟨_, by xrun [o₅.env.ebp, L.aW, aW], ?_⟩
    have fx : Frame (oF q.1.1) s₅.mem (s₅.mem.writeW (w64 (q.1.1.2 8) + BitVec.ofNat 64 auxO) (s₅.gpr .eax)) :=
      (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    have fx₁ : Frame [⟨w64 (q.1.1.2 8) + BitVec.ofNat 64 auxO, 4⟩] s₅.mem
        (s₅.mem.writeW (w64 (q.1.1.2 8) + BitVec.ofNat 64 auxO) (s₅.gpr .eax)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have sg : ∀ {o : Nat}, 80 ≤ o → o + 16 ≤ 2560 → ∀ r ∈ [(⟨w64 (q.1.1.2 8) + BitVec.ofNat 64 o, 16⟩ : Region)],
        (⟨w64 (stOf (q.1.1.2 8)) + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact st48_w G h₁ h₂
    refine ⟨o₅.frame G (by mems []; exact Frame.oD fx) (by regs []) (by regs []) (by regs []) (by mems [])
      (by mems []), hx, by mems [slotv_eq]; exact a₅', ?_, ?_, ?_⟩
    · mems []
      rw [a₅']
      cases q.2 <;> rfl
    · mems []
      rw [blockAt_frame fx₁ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact st48_w G (by decide) (by decide),
        blockAt_frame f₅ (sg (by decide) (by decide)), blockAt_frame f₄ (sg (by decide) (by decide)),
        blockAt_frame fT (cb_oT G (.inr rfl))]
      exact ha.cb
    · mems []
      rw [bytesAt_frame fx₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact G.d_w.sub_right (Lay.wSub (by decide)))
          (by have := G.fd; omega),
        bytesAt_frame fo₅ (d_oF G) (by have := G.fd; omega), bytesAt_frame fo₄ (d_oF G) (by have := G.fd; omega),
        bytesAt_frame (oT_oF fT) (d_woF G (by decide)) (by have := G.fd; omega)]
      exact hc₂
  -- The data decrypted if the tags are equal.
  refine Pc.seq (Q := OD M.Pre M.x M.out M.fb q) (Pc.ite (!q.2) (fun _ _ h => h.zf) (fun hb => ?_)
    (fun hb => ?_)) ?_
  · exact M.hfail q (by simpa using hb)
  · exact M.hdec q (by simpa using hb)
  -- The result.
  refine Pc.taint [.ebp] (fun s₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by native_taint_decide)
  have aR := h.o.env.wIn' (d := auxO) (n := 4) (by decide)
  have hv := h.aux
  rw [slotv_eq] at hv
  simp only [auxO] at hv aR
  refine WP.of_runBlock ⟨_, by xrun [h.o.env.ebp, L.aW, aR, hv], ?_⟩
  refine ⟨h.o.frame G (by mems []; exact Frame.refl _ _) (by regs []) (by regs []) (by regs []) (by mems [])
    (by mems []), h.ix, ?_⟩
  have hq2 := h.ix.q2 hT'
  simp only [PostO, oRes_ok hT']
  rw [M.out_mem (s := s) _ _ (by mems [])]
  by_cases hX : (tagOf q.1.1 s₀).take (q.1.1.2 9).toNat = rcvOf q.1.1 s₀
  · have h2 : q.2 = true := by rw [hq2]; simpa using hX
    have := h.out
    rw [h2] at this
    simp only [hX, ↓reduceIte, h2]
    exact ⟨by regs []; rfl, by simpa using this⟩
  · have h2 : q.2 = false := by rw [hq2]; simpa using hX
    have := h.out
    rw [h2] at this
    simp only [hX, ↓reduceIte, h2]
    exact ⟨by regs []; rfl, by simpa using this⟩
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s ⟨o, hx, hpost⟩ => ?_) (fun _ _ s₁ s₂ ⟨o₁, _⟩ ⟨o₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [o₁.env.ebp, o₂.env.ebp]) (by native_taint_decide)
  have esp := pubSw_esp hx.pub
  refine WP.mono (exit_ok o.env.ebp (by rw [o.env.esp, esp]) (covers_left o.env.wW) L.fw o.saved
    (by rw [esp]; exact o.ret)) fun s' ⟨abi, m', ax, _, _⟩ => ⟨abi, hx, ?_⟩
  unfold PostO at hpost ⊢
  rw [M.out_mem _ _ m', ax]
  exact hpost

/-! ## In place: `vg_aes_gcm_open` -/

/-- `open`'s body run in place: the data decrypted where they are, and left
as they were if the tag is wrong. -/
def inPlace (vg : GcmImpl) : OMode vg where
  Pre := openPre
  op := fun _ h => op_of_open h
  tg := fun _ h => openPre_tag h
  x := fun _ => 0
  out := fun p _ s => bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat
  fb := fun p s₀ => bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat
  out_mem := fun _ _ _ _ h => by rw [h]
  bad := .block [.mov .eax (imm 0)]
  fail := .block []
  dec := oneCrypt vg.callees
  hbad := fun q _ => by
    refine Pc.taint [.ebp] (fun s₀ s ⟨h, _, hx, _⟩ => WP.of_runBlock ⟨_, by xrun [], ?_⟩)
      (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by native_taint_decide)
    have G : OL q.1.1 := (op_of_open hx.pre).ol rfl (by decide) hx.pub
    exact ⟨h.o.frame G (by mems []; exact Frame.refl _ _) (by regs []) (by regs []) (by regs []) (by mems [])
      (by mems []), hx, by regs []; rfl, by mems []; exact h.data⟩
  hfail := fun q hf => Pc.mono Pc.nil (fun _ _ h => h) fun s₀ s h => ⟨h.o, h.ix, h.aux, by rw [hf]; exact h.data⟩
  hdec := fun q ht => by
    by_cases hex : ∃ s₀ s, OC openPre (fun _ => 0) q s₀ s
    swap
    · exact Pc.vacuous fun a s h => hex ⟨a, s, h⟩
    obtain ⟨z, w, hz⟩ := hex
    have G : OL q.1.1 := (op_of_open hz.ix.pre).ol rfl (by decide) hz.ix.pub
    have D : OLD q.1.1 := (opd_of_open hz.ix.pre).old (by decide) hz.ix.pub
    have L := G.L
    refine Pc.mono (Pc.lift (oneCrypt_pc G D (fun s₀ => inc32 (jOf q.1.1 s₀))) (fun s₀ s => (s₀, s))
      fun s₀ s h => ⟨⟨h.o, Proof.Gcm.ctr_zero _ _ _ _ h.cb, by
        rw [h.o.wr, ← open_arg h.ix.pub (i := 6) (by decide), ← open_arg h.ix.pub (i := 7) (by decide)]
        exact openPre_data h.ix.pre⟩, rfl⟩) (fun _ _ h => h)
      fun s₀ s' ⟨s, h, ⟨o', hd, fC⟩, _⟩ => ⟨o', h.ix, ?_, ?_⟩
    · rw [slotv_eq, slot_frame fC fun r hr => ?_, ← slotv_eq]
      · exact h.aux
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (G.d_w.sub_right (Lay.wSub (by decide))).symm
        · rw [st_eq G]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w (by decide)).symm
    · show bytesAt s'.mem _ _ = _
      rw [hd, h.data, ht, Proof.Gcm.gctr_eq]; rfl

theorem open_eq : «open» vg.callees = openBody vg.callees (inPlace vg).bad (inPlace vg).fail (inPlace vg).dec := rfl

theorem open_pc (q : OQ) :
    Pc (fun (s₀ : State) s => openPre s₀ ∧ ((pubSw 11 8 s₀, (0 : BitVec 32)), (openRes s₀).isSome) = q ∧ s = s₀)
      («open» vg.callees) (fun s₀ s' => abiPreserved s₀ s' ∧ openX86.post s₀ s') := by
  rw [open_eq]
  refine Pc.mono (openBody_pc (inPlace vg) q) (fun _ _ h => h) fun s₀ s' ⟨abi, hx, hpost⟩ => ⟨abi, ?_⟩
  simp only [openX86, ret32_eq]
  rw [openRes_eq hx.pub, open_arg hx.pub (i := 6) (by decide), open_arg hx.pub (i := 7) (by decide)]
  exact hpost

theorem open_correct (s : State) (hs : openX86.pre s) :
    ∃ t s', Exec isa («open» vg.callees) s t s' ∧ abiPreserved s s' ∧ openX86.post s s' :=
  (open_pc ((pubSw 11 8 s, 0), (openRes s).isSome)).wp s s ⟨hs, rfl, rfl⟩

theorem open_ct : ConstantTime isa openX86.pre openX86.pub («open» vg.callees) :=
  Pc.constantTime (fun s => ((pubSw 11 8 s, (0 : BitVec 32)), (openRes s).isSome))
    (fun _ _ _ _ h => by rw [pubSw_eq (by decide) h.1, h.2]) open_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86
