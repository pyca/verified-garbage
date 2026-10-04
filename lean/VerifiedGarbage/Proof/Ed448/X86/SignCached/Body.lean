import VerifiedGarbage.Proof.Ed448.X86.SignCached.Calls
import VerifiedGarbage.Proof.Ed448.X86.Shake.Prune
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe

/-!
# Ed448 signing with a cached key on x86 (32-bit): correctness

The steps of `body` in order (`Impl/Ed448/X86/SignCached.lean`), each with
what it leaves and what it writes; the values the later steps use are
carried past the steps in between (each outside what they write), and the
signature is `Spec.Ed448.sign`'s by `Proof.Ed448.sign_pipeline`.
`signCached_ok`: the whole function, in Ed25519's frame on this target.
-/

namespace VG.Proof.Ed448.X86.SignCached

open VG VG.X86 VG.Impl.Ed448.X86.SignCached
open VG.Impl.Ed448.X86.Shake (callWith hdrAt pruneAt)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.Within Whole.FR Whole.Ctx.zeroWords)

variable {s t : State} {g : Reg → BitVec 32} {m : Mem}

theorem drop57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  have e := Proof.X25519.bytesAt_add m p 57 57
  have l := Proof.X25519.length_bytesAt m p 57
  rw [Proof.Ed448.bytesAt_eq, Proof.Ed448.bytesAt_eq, show (114 : Nat) = 57 + 57 from rfl, e,
    List.drop_left' l]

theorem split114 (m : Mem) (p : Addr) :
    Spec.Ed448.bytesAt m p 114 = Spec.Ed448.bytesAt m p 57 ++ Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [Proof.Ed448.bytesAt_eq, Proof.Ed448.bytesAt_eq, Proof.Ed448.bytesAt_eq,
    show (114 : Nat) = 57 + 57 from rfl, Proof.X25519.bytesAt_add]

section
variable (h : Facts s)
include h

/-! ## What each step writes, and what it does not -/

theorem dW {D : Region} {d : Nat} (hlo : (Lo (base s)).Disjoint D) (hfr : D.Disjoint (fr (base s) d 114))
    (hscr : D.Disjoint (SCR (arg s 7))) : ∀ r ∈ W s d, D.Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hlo.symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hfr
  · exact hscr.sub_right ((kit h).kWr_sub r hr).sub

omit h in
theorem d3 {D a b c : Region} (ha : D.Disjoint a) (hb : D.Disjoint b) (hc : D.Disjoint c) :
    ∀ r ∈ [a, b, c], D.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [ha, hb, hc]

omit h in
theorem d1 {D a : Region} (ha : D.Disjoint a) : ∀ r ∈ [a], D.Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]; exact ha

theorem fr_out {d : Nat} (hd : d + 57 ≤ 256) : (fr (base s) d 57).Disjoint (OUT s) :=
  ((kit h).ko _ (out_in s)).sub_left (frame_sub_stk _ hd)

theorem fr_out1 {d : Nat} (hd : d + 57 ≤ 256) : (fr (base s) d 57).Disjoint (OUT1 s) :=
  (fr_out h hd).sub_right (out1_within s).sub

theorem fr_out2 {d : Nat} (hd : d + 57 ≤ 256) : (fr (base s) d 57).Disjoint (OUT2 s) :=
  (fr_out h hd).sub_right (out2_within s).sub

theorem out_fr {d l : Nat} (hd : d + l ≤ 256) : (OUT s).Disjoint (fr (base s) d l) :=
  (((kit h).ko _ (out_in s)).sub_left (frame_sub_stk _ hd)).symm

/-! ## The scalar steps -/

theorem r_step (hc : GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) t fun u => GCtx s g m u ∧
      Frame [OUT2 s, SCR (arg s 7), Lo (base s)] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (r_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (r_call h hu hs) fun v ⟨hv, hf, ho⟩ => ⟨hv, ?_, ?_⟩
  · refine (hm.sub fun r hr => ⟨Lo (base s), by simp, ?_⟩).trans hf
    rw [List.mem_singleton.mp hr]; exact args_lo _ (by decide)
  · rw [ho, frame_bytes hm (D := fr (base s) HASH 114) (d1 (Offset.disjoint_base _ (by decide) (by decide)))
      (by show 114 ≤ 2 ^ 64; decide)]

theorem b_step {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (hc : GCtx s g m t)
    (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (callWith baseArgs "vg_ed448_scalar_base" base') t fun u => GCtx s g m u ∧
      Frame [OUT1 s, SCR (arg s 7), Lo (base s)] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64) 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57) := by
  refine WP.seq (WP.mono (b_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (b_call h hB hu hs) fun v ⟨hv, hf, ho⟩ => ⟨hv, ?_, ?_⟩
  · refine (hm.sub fun r hr => ⟨Lo (base s), by simp, ?_⟩).trans hf
    rw [List.mem_singleton.mp hr]; exact args_lo _ (by decide)
  · rw [ho, frame_bytes hm (D := OUT2 s) (d1 ((out2_lo h).sub_left (args_lo _ (by decide))).symm)
      (by show 57 ≤ 2 ^ 64; decide)]

theorem k_step (hc : GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) t fun u => GCtx s g m u ∧
      Frame [fr (base s) K 57, SCR (arg s 7), Lo (base s)] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (k_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (k_call h hu hs) fun v ⟨hv, hf, ho⟩ => ⟨hv, ?_, ?_⟩
  · refine (hm.sub fun r hr => ⟨Lo (base s), by simp, ?_⟩).trans hf
    rw [List.mem_singleton.mp hr]; exact args_lo _ (by decide)
  · rw [ho, frame_bytes hm (D := fr (base s) HASH 114) (d1 (Offset.disjoint_base _ (by decide) (by decide)))
      (by show 114 ≤ 2 ^ 64; decide)]

theorem m_step (hc : GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.X86.scalarMulAdd) t fun u => GCtx s g m u ∧
      Frame [OUT2 s, SCR (arg s 7), Lo (base s)] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57)
          (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57)
          (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 S) 57) := by
  refine WP.seq (WP.mono (m_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (m_call h hu hs) fun v ⟨hv, hf, ho⟩ => ⟨hv, ?_, ?_⟩
  · refine (hm.sub fun r hr => ⟨Lo (base s), by simp, ?_⟩).trans hf
    rw [List.mem_singleton.mp hr]; exact args_lo _ (by decide)
  · rw [ho, frame_bytes hm (D := OUT2 s) (d1 ((out2_lo h).sub_left (args_lo _ (by decide))).symm)
      (by show 57 ≤ 2 ^ 64; decide),
      frame_bytes hm (D := fr (base s) K 57) (d1 (Offset.disjoint_base _ (by decide) (by decide)))
      (by show 57 ≤ 2 ^ 64; decide),
      frame_bytes hm (D := fr (base s) S 57) (d1 (Offset.disjoint_base _ (by decide) (by decide)))
      (by show 57 ≤ 2 ^ 64; decide)]

/-! ## The body -/

theorem body_ok {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (hc : GCtx s g m t)
    (ha : Shake.Args (base s) 8 (arg s) m)
    (hkey : Spec.Ed448.bytesAt m ((arg s 2).setWidth 64) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57)) :
    WP isa (body base') t fun u => GCtx s g m u ∧
      Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64) 114 = Spec.Ed448.sign
        (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57)
        (Spec.Ed448.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat)
        (Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat) := by
  have hk := kit h
  have hcl : (arg s 4).toNat < 256 := by have := h.ctxlen; omega
  -- Disjointness of the values carried.
  have lS := lo_fr (base s) (d := S) (l := 57) (by decide) (by decide)
  have lK := lo_fr (base s) (d := K) (l := 57) (by decide) (by decide)
  have sS : (fr (base s) S 57).Disjoint (SCR (arg s 7)) := hk.fr_scr (by decide)
  have sK : (fr (base s) K 57).Disjoint (SCR (arg s 7)) := hk.fr_scr (by decide)
  have o1W : ∀ {d : Nat}, d + 114 ≤ 256 → ∀ r ∈ W s d, (OUT1 s).Disjoint r := fun hd =>
    dW h (out1_lo h) ((out_fr h hd).sub_left (out1_within s).sub) (out1_scr h)
  have o2W : ∀ {d : Nat}, d + 114 ≤ 256 → ∀ r ∈ W s d, (OUT2 s).Disjoint r := fun hd =>
    dW h (out2_lo h) ((out_fr h hd).sub_left (out2_within s).sub) (out2_scr h)
  have n57 : (57 : Nat) ≤ 2 ^ 64 := by decide
  unfold body
  -- `SHAKE256(seed, 114)` at `S`.
  refine WP.seq (WP.mono (seed_ok h hc ha) fun t1 ⟨hc1, _, hs1⟩ => ?_)
  have hs1' : Spec.Ed448.bytesAt t1.mem ((base s).setWidth 64 + BitVec.ofNat 64 S) 114 =
      Spec.Sha3.shake256 (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57) 114 := hs1
  -- `s`, pruned in place; the prefix at `K`.
  refine WP.seq (WP.mono (hk.prune_ok hc1 (q := S) (by decide)) fun t2 ⟨hc2, hf2, hp2, _⟩ => ?_)
  rw [hs1'] at hp2
  have pf2 : Spec.Ed448.bytesAt t2.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 =
      (Spec.Sha3.shake256 (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57) 114).drop 57 := by
    rw [frame_bytes hf2 (D := fr (base s) K 57) (d1 (Offset.disjoint _ (by decide) (by decide) (by decide))) n57,
      ← hs1', drop57, Offset.add_add]
    rfl
  -- The header.
  refine WP.seq (WP.mono (hk.hdr_ok hc2 ha (j := 4) (off := HASH) (by decide) hcl (by decide))
    fun t3 ⟨hc3, hf3, hh3, _⟩ => ?_)
  have sp3 := (frame_bytes hf3 (D := fr (base s) S 57) (d1 (Offset.disjoint _ (by decide) (by decide) (by decide)))
    n57)
  have pf3 := (frame_bytes hf3 (D := fr (base s) K 57) (d1 (Offset.disjoint _ (by decide) (by decide) (by decide)))
    n57).trans pf2
  -- The nonce's hash at `HASH`.
  refine WP.seq (WP.mono (nonce_ok h hc3 ha hh3 pf3) fun t4 ⟨hc4, hf4, hn4⟩ => ?_)
  have sp4 := (frame_bytes hf4 (D := fr (base s) S 57)
    (dW h lS (Offset.disjoint _ (by decide) (by decide) (by decide)) sS) n57).trans sp3
  -- `r` into the second half of `out`.
  refine WP.seq (WP.mono (r_step h hc4 ha) fun t5 ⟨hc5, hf5, hr5⟩ => ?_)
  have sp5 := (frame_bytes hf5 (D := fr (base s) S 57) (d3 (fr_out2 h (by decide)) sS lS.symm) n57).trans sp4
  -- `R` into the first half.
  refine WP.seq (WP.mono (b_step h hB hc5 ha) fun t6 ⟨hc6, hf6, hR6⟩ => ?_)
  have sp6 := (frame_bytes hf6 (D := fr (base s) S 57) (d3 (fr_out1 h (by decide)) sS lS.symm) n57).trans sp5
  have r6 := (frame_bytes hf6 (D := OUT2 s) (d3 (out12 s).symm (out2_scr h) (out2_lo h).symm) n57).trans hr5
  -- The header again.
  refine WP.seq (WP.mono (hk.hdr_ok hc6 ha (j := 4) (off := HASH) (by decide) hcl (by decide))
    fun t7 ⟨hc7, hf7, hh7, _⟩ => ?_)
  have sp7 := (frame_bytes hf7 (D := fr (base s) S 57) (d1 (Offset.disjoint _ (by decide) (by decide) (by decide)))
    n57).trans sp6
  have r7 := (frame_bytes hf7 (D := OUT2 s) (d1 ((out_fr h (by decide)).sub_left (out2_within s).sub)) n57).trans r6
  have R7 := (frame_bytes hf7 (D := OUT1 s) (d1 ((out_fr h (by decide)).sub_left (out1_within s).sub)) n57).trans hR6
  -- The challenge's hash at `HASH`.
  refine WP.seq (WP.mono (chal_ok h hc7 ha hh7 R7) fun t8 ⟨hc8, hf8, hn8⟩ => ?_)
  have sp8 := (frame_bytes hf8 (D := fr (base s) S 57)
    (dW h lS (Offset.disjoint _ (by decide) (by decide) (by decide)) sS) n57).trans sp7
  have r8 := (frame_bytes hf8 (D := OUT2 s) (o2W (by decide)) n57).trans r7
  have R8 := (frame_bytes hf8 (D := OUT1 s) (o1W (by decide)) n57).trans R7
  -- `k` at `K`.
  refine WP.seq (WP.mono (k_step h hc8 ha) fun t9 ⟨hc9, hf9, hk9⟩ => ?_)
  have sp9 := (frame_bytes hf9 (D := fr (base s) S 57)
    (d3 (Offset.disjoint _ (by decide) (by decide) (by decide)) sS lS.symm) n57).trans sp8
  have r9 := (frame_bytes hf9 (D := OUT2 s) (d3 (fr_out2 h (by decide)).symm (out2_scr h) (out2_lo h).symm) n57).trans r8
  have R9 := (frame_bytes hf9 (D := OUT1 s) (d3 (fr_out1 h (by decide)).symm (out1_scr h) (out1_lo h).symm) n57).trans R8
  -- `S` over `r`.
  refine WP.seq (WP.mono (m_step h hc9 ha) fun t10 ⟨hc10, hf10, hS10⟩ => ?_)
  have R10 := (frame_bytes hf10 (D := OUT1 s) (d3 (out12 s) (out1_scr h) (out1_lo h).symm) n57).trans R9
  -- The frame cleared.
  refine WP.mono (Whole.Ctx.zeroWords hc10 (start := 6) (count := 58) hk.frame (by decide)) fun u ⟨hu, hf, _⟩ =>
    ⟨hu, ?_⟩
  have keep := frame_bytes hf (D := OUT s) (d1 (out_fr h (d := 4 * 6) (l := 4 * 58) (by decide)))
    (by show 114 ≤ 2 ^ 64; decide)
  rw [keep, split114, R10, hS10, r9, hk9, hr5]
  have hn8' : Spec.Ed448.bytesAt t8.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
      Spec.Ed448.hash (Spec.Ed448.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat)
        (Spec.Ed448.scalarBase (Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t4.mem
            ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114)) ++
          Spec.Ed448.bytesAt m ((arg s 2).setWidth 64) 57 ++
          Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat) := by
    rw [show Spec.Ed448.bytesAt t8.mem _ 114 = _ from hn8, ← hr5]
    rfl
  have hn4' : Spec.Ed448.bytesAt t4.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
      Spec.Ed448.hash (Spec.Ed448.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat)
        ((Spec.Sha3.shake256 (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57) 114).drop 57 ++
          Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat) := hn4
  rw [hn8', hn4', hkey]
  exact Proof.Ed448.sign_pipeline _ _ _ _ _ rfl (by rw [sp9]; exact hp2)

end

theorem body_nosp {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') : NoSp (body base') := by
  have z : NoSp (Impl.Ed448.X86.Shake.zeroState SC) := NoSp.of_all (by decide +kernel)
  have hdr : NoSp (.block (hdrAt 4 HASH)) := NoSp.of_all (by decide +kernel)
  have pr : NoSp (.block (pruneAt S)) := NoSp.of_all (by decide +kernel)
  have pd : NoSp (Impl.Ed448.X86.Shake.pad SC) := pad_nosp' (NoSp.of_all (by decide +kernel))
  have sqS : NoSp (Impl.Ed448.X86.Shake.squeeze SC S) := squeeze_nosp' (NoSp.of_all (by decide +kernel))
  have sqH : NoSp (Impl.Ed448.X86.Shake.squeeze SC HASH) := squeeze_nosp' (NoSp.of_all (by decide +kernel))
  have sh : NoSp seedHash :=
    nosp_seq z (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel))) (nosp_seq pd sqS))
  have nh : NoSp nonceHash :=
    nosp_seq z (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
      (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
        (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
          (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel))) (nosp_seq pd sqH)))))
  have ch : NoSp chalHash :=
    nosp_seq z (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
      (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
        (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
          (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
            (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel))) (nosp_seq pd sqH))))))
  have rr : NoSp (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) :=
    nosp_seq (NoSp.of_all (by decide +kernel)) reduce_nosp
  have bb : NoSp (callWith baseArgs "vg_ed448_scalar_base" base') :=
    nosp_seq (NoSp.of_all (by decide +kernel)) hB.nosp
  have rk : NoSp (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) :=
    nosp_seq (NoSp.of_all (by decide +kernel)) reduce_nosp
  have ma : NoSp (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.X86.scalarMulAdd) :=
    nosp_seq (NoSp.of_all (by decide +kernel)) mulAdd_nosp
  have wp : NoSp (.block wipe) := NoSp.of_all (by decide +kernel)
  exact nosp_seq sh (nosp_seq pr (nosp_seq hdr (nosp_seq nh (nosp_seq rr (nosp_seq bb (nosp_seq hdr
    (nosp_seq ch (nosp_seq rk (nosp_seq ma wp)))))))))

theorem signCached_ok {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') {s : State} (hp : scLocal.pre s) :
    WP isa (code base') s fun t => abiPreserved s t ∧ scLocal.post s t := by
  have h := facts hp
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; have := h.below; omega) (body_nosp hB)
    (WP.mono (body_ok h hB (push_ctx hp.1 hp.2.1 h.below) (args_val s 8) h.key) fun u ⟨hu, ho⟩ =>
      ⟨pop_abi (by decide) h.below hu (ret_out h), ?_⟩)
  change Spec.Ed448.bytesAt (popped .eax (List.replicate 64 .eax).length u).mem ((arg s 0).setWidth 64) 114 = _
  rw [popped_mem]
  exact ho

end VG.Proof.Ed448.X86.SignCached
