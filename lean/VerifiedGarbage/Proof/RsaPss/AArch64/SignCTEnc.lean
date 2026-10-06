import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTBase
import VerifiedGarbage.Proof.RsaPss.AArch64.RelSplit

/-!
# RSASSA-PSS signing on AArch64: the encoding is constant time

`signEnc_ct`: two runs of the encoding from states with the same public
data leak the same trace. Between its pieces, each run is described by the
registers and slots of the frame that the anchor's public data fix (`SR`);
the pieces are checked by the taint analysis from those registers, the loads
of the salt's address and length from the frame are related by correctness
(`RelCT.seq_block_append`), the hash by `ctHash_ct` and MGF1 by `mgfXor_ct`.
-/

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_add wp_sub wp_subImm wp_strb eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite wp_ldrSp wp_mov)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off loV maskV two_taintE zH Lay slot_keep slotR mgfWr PssChecks HA HE MA MS
  dbRegs_ok clearY_ok copyDigest_ok copySaltY_ok signLen_ok clearEm_ok putSalt_ok putH_ok clearTop_ok
  ctHash_ct mgfXor_ct mgfXor_ok ctHashWith_out two_step pins_nil pad80_ok nb_keep slot_not_below wS_frame off_sub off_add ld_slot
  DbAt)

/-! ## The public values -/

/-- `k`, `lo`, `dbLen`, `sLen` and the number of blocks of `M'`, from the
anchor. -/
abbrev kA (a : State) : Nat := (a.gpr .x3).toNat
abbrev loA (a : State) : Nat := loV (nx a)
abbrev dbA (D : Nat) (a : State) : Nat := kA a - loA a - D - 1
abbrev slA (a : State) : Nat := (stackArg a 10).toNat
abbrev nbA (H : Hash) (a : State) : Nat := (8 + H.D + slA a + H.P.L) / H.P.B + 1

/-- The encoding fits: the checks passed. -/
structure SOk (D : Nat) (a : State) : Prop where
  h0 : nx a ≠ 0
  k1 : 64 ≤ kA a
  k2 : kA a ≤ 1024
  fit : D + slA a + 2 ≤ kA a - loA a

/-- A run of the encoding, from an entry state with the anchor's public
data: the frame and the working space, and registers (`rs`) and slots (`sl`)
the anchor fixes. -/
structure SR (D K : Nat) (rs : List (Reg × (State → BitVec 64))) (sl : List (Nat × (State → BitVec 64)))
    (a t : State) : Prop where
  ex : ∃ s, E D K a s ∧ t.rd = s.rd ∧ t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  L : Lay t (fb a) (scr a)
  r : ∀ q ∈ rs, t.gpr q.1 = q.2 a
  sl : ∀ q ∈ sl, t.mem.readW (off (fb a) q.1) 64 = q.2 a
  ok : SOk D a

theorem SR.pins {D K : Nat} {rs : List (Reg × (State → BitVec 64))} {sl : List (Nat × (State → BitVec 64))}
    {qs : List Reg} (h : ∀ r ∈ qs, r = .x20 ∨ ∃ f, (r, f) ∈ rs) : Pins (SR D K rs sl) qs :=
  fun a s₁ s₂ h₁ h₂ => by
    refine ⟨by rw [h₁.L.sp, h₂.L.sp], fun r hr => ?_⟩
    rcases h r hr with rfl | ⟨f, hf⟩
    · rw [h₁.L.x20, h₂.L.x20]
    · rw [h₁.r _ hf, h₂.r _ hf]

theorem SR.keep {D K : Nat} {rs : List (Reg × (State → BitVec 64))} {sl : List (Nat × (State → BitVec 64))}
    {a u u' : State} (h : SR D K rs sl a u) {ks : List Reg} (k : Keep ks u u') (hk : ∀ q ∈ rs, q.1 ∉ ks)
    (h20 : Reg.x20 ∉ ks) {ws : List Region} (hf : Frame ws u.mem u'.mem)
    (hs : ∀ q ∈ sl, ∀ r ∈ ws, Region.Disjoint (slotR (fb a) q.1) r) : SR D K rs sl a u' where
  ex := let ⟨s, e, hrd, hwr⟩ := h.ex; ⟨s, e, k.rd.trans hrd, k.wr.trans hwr⟩
  L := h.L.congr k.sp k.wr (k.gpr .x20 h20)
  r := fun q hq => by rw [k.gpr q.1 (hk q hq)]; exact h.r q hq
  sl := fun q hq => by rw [slot_keep hf (hs q hq)]; exact h.sl q hq
  ok := h.ok

/-- The registers of the encoding: `st`, the digest, `k`, `DB` and `dbLen`. -/
def sregs (D : Nat) : List (Reg × (State → BitVec 64)) :=
  [(.x19, fun a => off (scr a) oSt), (.x21, fun a => off (scr a) oDig), (.x23, fun a => a.gpr .x3),
    (.x24, fun a => off (scr a) (oEm + loA a)), (.x25, fun a => BitVec.ofNat 64 (dbA D a))]

theorem sregs_fst {D : Nat} {q : Reg × (State → BitVec 64)} (hq : q ∈ sregs D) :
    q.1 ∈ [Reg.x19, .x21, .x23, .x24, .x25] := by
  simp only [sregs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp

/-- Registers apart from the encoding's, for `decide`. -/
theorem nk_of {D : Nat} {ks : List Reg} (h : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∉ ks) :
    ∀ q ∈ sregs D, q.1 ∉ ks :=
  fun _ hq => h _ (sregs_fst hq)

/-- The slots it reads: the digest's and the salt's addresses, the salt's
length and `lo`. -/
def sslots : List (Nat × (State → BitVec 64)) :=
  [(sDig, fun a => stackArg a 8), (sSalt, fun a => stackArg a 9), (sSaltLen, fun a => stackArg a 10),
    (sLo, fun a => BitVec.ofNat 64 (loA a))]

theorem sslots_S {F S : Addr} {t : State} (L : Lay t F S) :
    ∀ q ∈ sslots, ∀ r ∈ [(⟨S, oRsa⟩ : Region)], Region.Disjoint (slotR F q.1) r := by
  intro q hq r hr
  rw [List.mem_singleton.mp hr]
  simp only [sslots, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> exact L.dFS.sub_left (Offset.sub_base F (by decide))


/-- `SR` at a later state of the same run, from what it says there. -/
theorem SR.congr {D K : Nat} {rs rs' : List (Reg × (State → BitVec 64))} {sl sl' : List (Nat × (State → BitVec 64))}
    {a u u' : State} (h : SR D K rs sl a u) (sp : u'.sp = u.sp) (rd : u'.rd = u.rd) (wr : u'.wr = u.wr)
    (h20 : u'.gpr .x20 = u.gpr .x20) (hr : ∀ q ∈ rs', u'.gpr q.1 = q.2 a)
    (hs : ∀ q ∈ sl', u'.mem.readW (off (fb a) q.1) 64 = q.2 a) : SR D K rs' sl' a u' where
  ex := let ⟨s, e, hrd, hwr⟩ := h.ex; ⟨s, e, rd.trans hrd, wr.trans hwr⟩
  L := h.L.congr sp wr h20
  r := hr
  sl := hs
  ok := h.ok

namespace SR
variable {D K : Nat} {rs : List (Reg × (State → BitVec 64))} {sl : List (Nat × (State → BitVec 64))}
  {a u : State} (h : SR D K rs sl a u)
include h

/-- The digest is readable and apart from our working space. -/
theorem dig : (∀ j < D, InRegions (u.rd ++ u.wr) (stackArg a 8 + BitVec.ofNat 64 j) 1) ∧
    Region.Disjoint ⟨stackArg a 8, D⟩ ⟨scr a, oRsa⟩ := by
  obtain ⟨s, e, hrd, hwr⟩ := h.ex
  have hp := e.1
  rw [← e.2.args 8 (by decide), ← e.scr]
  refine ⟨fun j hj => ?_, hp.dgs.sub_right (rsa_sub hp)⟩
  rw [hrd, hwr]
  exact Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _
    ⟨dgR D s, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by have := hp.wdg; omega)⟩

/-- The salt is readable and apart from what the encoding writes. -/
theorem salt : (∀ j < slA a, InRegions (u.rd ++ u.wr) (stackArg a 9 + BitVec.ofNat 64 j) 1) ∧
    Region.Disjoint ⟨stackArg a 9, slA a⟩ ⟨scr a, oRsa⟩ := by
  obtain ⟨s, e, hrd, hwr⟩ := h.ex
  have hp := e.1
  rw [← e.2.args 9 (by decide), slA, ← e.2.args 10 (by decide), ← e.scr]
  refine ⟨fun j hj => ?_, hp.sls.sub_right (rsa_sub hp)⟩
  rw [hrd, hwr]
  exact Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _
    ⟨slR s, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by have := hp.wsl; omega)⟩

theorem sl_le : slA a ≤ 1024 := by have := h.ok.fit; have := h.ok.k2; omega

theorem x23 (h23 : (Reg.x23, fun a : State => a.gpr .x3) ∈ rs) : u.gpr .x23 = BitVec.ofNat 64 (kA a) := by
  rw [h.r _ h23, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end SR

theorem SR.sp {D K : Nat} {rs : List (Reg × (State → BitVec 64))} {sl : List (Nat × (State → BitVec 64))} :
    ∀ a s₁ s₂, SR D K rs sl a s₁ → SR D K rs sl a s₂ → s₁.sp = s₂.sp :=
  fun _ _ _ h₁ h₂ => by rw [h₁.L.sp, h₂.L.sp]

/-! ## The pieces -/

/-- At the start of the encoding: `emLen - hLen - 2` in `x9`. -/
def sregs0 (D : Nat) : List (Reg × (State → BitVec 64)) :=
  [(.x19, fun a => off (scr a) oSt), (.x21, fun a => off (scr a) oDig), (.x23, fun a => a.gpr .x3),
    (.x9, fun a => BitVec.ofNat 64 (kA a - loA a - (D + 2)))]

theorem dbRegs_sct {D K : Nat} :
    RelCT isa (Two (SR D K (sregs0 D) sslots)) (.block dbRegs) (Two (SR D K (sregs D) sslots)) := by
  refine two_post (two_taint [] (pins_nil SR.sp) (by taint_decide)) fun a u h => ?_
  have hf := h.ok.fit
  refine WP.mono (dbRegs_ok h.L (x := kA a - loA a - (D + 2)) (lo := loA a)
    (h.r (.x9, fun a => BitVec.ofNat 64 (kA a - loA a - (D + 2))) (by simp [sregs0]))
    (h.sl (sLo, fun a => BitVec.ofNat 64 (loA a)) (by simp [sslots]))) fun u' ⟨O, x25, x24⟩ =>
    h.congr O.sp O.rd O.wr (O.get .x20) (fun q hq => ?_) fun q hq => by rw [O.mem]; exact h.sl q hq
  simp only [sregs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · rw [O.get .x19]; exact h.r (.x19, fun a => off (scr a) oSt) (by simp [sregs0])
  · rw [O.get .x21]; exact h.r (.x21, fun a => off (scr a) oDig) (by simp [sregs0])
  · rw [O.get .x23]; exact h.r (.x23, fun a => a.gpr .x3) (by simp [sregs0])
  · exact x24
  · rw [x25]; show _ = BitVec.ofNat 64 (kA a - loA a - D - 1)
    rw [show kA a - loA a - (D + 2) + 1 = kA a - loA a - D - 1 by omega]

theorem clearY_sct {D K : Nat} :
    RelCT isa (Two (SR D K (sregs D) sslots)) clearY (Two (SR D K (sregs D) sslots)) :=
  two_post (two_taint [.x20] (SR.pins fun r hr => by simp at hr; exact .inl hr) (by taint_decide))
    fun _ _ h => WP.mono (clearY_ok h.L (fun _ _ => rfl)) fun _ ⟨k, f, _⟩ =>
      h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L)

section
variable {H : Hash} (hH : HashOK H)

include hH in
theorem copyDigest_sct {K : Nat} :
    RelCT isa (Two (SR H.D K (sregs H.D) sslots)) (copyDigest H) (Two (SR H.D K (sregs H.D) sslots)) := by
  refine two_post ?_ fun a u h => WP.mono (copyDigest_ok hH h.L (fun _ _ => rfl) (dig := stackArg a 8)
    (h.sl (sDig, fun a => stackArg a 8) (by simp [sslots])) h.dig.1 h.dig.2) fun _ ⟨k, f, _⟩ =>
      h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L)
  unfold copyDigest
  refine RelCT.seq_block_append (M := isa) (l₁ := [ld .x11 sDig]) ?_
  refine two_step (Ψ := SR H.D K (sregs H.D ++ [(.x11, fun a => stackArg a 8)]) sslots)
    (two_taint [] (pins_nil SR.sp) (by taint_decide)) (fun a u h => ?_)
    (two_taintE [.x11, .x20] (SR.pins fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
      (c' := Code.eraseOff (.seq (.block [.addImm .x .x14 .x20 (oY + 8), movi .x12 zH.D])
        Impl.RsaPkcs1Sig.AArch64.copyLoop)) rfl (by taint_decide))
  have nk : ∀ q ∈ sregs H.D, q.1 ∉ [Reg.x11] := nk_of (by decide)
  unfold ld
  refine wp_ldrSp (by decide) (by rw [h.L.sp]; exact h.L.fld (by decide)) fun u' o e =>
    wp_nil (h.congr o.sp o.rd o.wr (o.get .x20) (fun q hq => ?_) fun q hq => by rw [o.mem]; exact h.sl q hq)
  rcases List.mem_append.mp hq with hq | hq
  · rw [o.get q.1 (nk q hq)]; exact h.r q hq
  · rw [List.mem_singleton.mp hq, e, h.L.sp]; exact h.sl (sDig, fun a => stackArg a 8) (by simp [sslots])

/-- After the salt's address, place and length are loaded. -/
def rsY (D : Nat) : List (Reg × (State → BitVec 64)) :=
  sregs D ++ [(.x11, fun a => stackArg a 9), (.x14, fun a => off (scr a) (oY + 8 + D)), (.x12, fun a => stackArg a 10)]

include hH in
theorem copySaltY_sct {K : Nat} :
    RelCT isa (Two (SR H.D K (sregs H.D) sslots)) (copySaltY H) (Two (SR H.D K (sregs H.D) sslots)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  refine two_post ?_ fun a u h => WP.mono (copySaltY_ok hH h.L (fun _ _ => rfl) (q := stackArg a 9) (sl := slA a)
    (h.sl (sSalt, fun a => stackArg a 9) (by simp [sslots]))
    (by rw [h.sl (sSaltLen, fun a => stackArg a 10) (by simp [sslots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    h.sl_le h.salt.1 h.salt.2) fun _ ⟨k, f, _⟩ => h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L)
  unfold copySaltY
  refine two_step (Ψ := SR H.D K (rsY H.D) sslots)
    (two_taintE [] (pins_nil SR.sp) (c' := Code.eraseOff (.block [ld .x11 sSalt, .addImm .x .x14 .x20 (oY + 8 + zH.D),
      ld .x12 sSaltLen])) rfl (by taint_decide)) (fun a u h => ?_) ?_
  · have nk : ∀ q ∈ sregs H.D, q.1 ∉ [Reg.x11, .x14, .x12] := nk_of (by decide)
    unfold ld
    refine wp_ldrSp (by decide) (ld_slot h.L (by decide)) fun u₁ o₁ e₁ => wp_addImm (by unfold oY; omega)
      fun u₂ o₂ e₂ => wp_ldrSp (by decide) (by rw [o₂.sp, o₂.rd, o₂.wr, o₁.sp, o₁.rd, o₁.wr]; exact ld_slot h.L (by decide))
        fun u₃ o₃ e₃ => wp_nil ?_
    have O : Only [.x11, .x14, .x12] u u₃ := (o₁.trans (o₂.trans o₃)).mono
    refine h.congr O.sp O.rd O.wr (O.get .x20) (fun q hq => ?_) fun q hq => by rw [O.mem]; exact h.sl q hq
    rcases List.mem_append.mp hq with hq | hq
    · rw [O.get q.1 (nk q hq)]; exact h.r q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · rw [o₃.get .x11, o₂.get .x11, e₁, h.L.sp]; exact h.sl (sSalt, fun a => stackArg a 9) (by simp [sslots])
      · rw [o₃.get .x14, e₂, o₁.get .x20, h.L.x20]
      · rw [e₃, o₂.mem, o₁.mem, o₂.sp, o₁.sp, h.L.sp]
        exact h.sl (sSaltLen, fun a => stackArg a 10) (by simp [sslots])
  · have p12 : ∀ a s, SR H.D K (rsY H.D) sslots a s → s.gpr .x12 = stackArg a 10 := fun a s h =>
      h.r (.x12, fun a => stackArg a 10) (by simp [rsY])
    refine two_ite (fun a s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, p12 a s₁ h₁, p12 a s₂ h₂])
      (two_taint [] (fun a s₁ s₂ h₁ h₂ => pins_nil SR.sp a s₁ s₂ h₁.1 h₂.1) (by taint_decide))
      (two_taint [.x11, .x12, .x14] (fun a s₁ s₂ h₁ h₂ => SR.pins (rs := rsY H.D) (fun r hr => by
        simp at hr; rcases hr with rfl | rfl | rfl <;> simp [rsY]) a s₁ s₂ h₁.1 h₂.1) (by taint_decide))

/-- After `signLen`: `ℓ` and the number of blocks of `M'`. -/
def rsL (D : Nat) : List (Reg × (State → BitVec 64)) := sregs D ++ [(.x22, fun a => BitVec.ofNat 64 (8 + D + slA a))]
def slL (H : Hash) : List (Nat × (State → BitVec 64)) := sslots ++ [(sNb, fun a => BitVec.ofNat 64 (nbA H a))]

include hH in
theorem signLen_sct {K : Nat} :
    RelCT isa (Two (SR H.D K (sregs H.D) sslots)) (.block (signLen H)) (Two (SR H.D K (rsL H.D) (slL H))) := by
  refine two_post (two_taintE [] (pins_nil SR.sp) (c' := Code.eraseOff (.block (signLen zH))) rfl (by taint_decide))
    fun a u h => WP.mono (signLen_ok hH h.L (sl := slA a)
      (by rw [h.sl (sSaltLen, fun a => stackArg a 10) (by simp [sslots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
      h.sl_le) fun u' ⟨k, x22, m⟩ => h.congr k.sp k.rd k.wr (k.get .x20) (fun q hq => ?_) fun q hq => ?_
  · have nk : ∀ q ∈ sregs H.D, q.1 ∉ [Reg.x9, .x22, .x16] := nk_of (by decide)
    rcases List.mem_append.mp hq with hq | hq
    · rw [k.get q.1 (nk q hq)]; exact h.r q hq
    · rw [List.mem_singleton.mp hq]; exact x22
  · rcases List.mem_append.mp hq with hq | hq
    · rw [m, slot_keep (frame_slot _ _ sNb _) fun r hr => ?_]
      · exact h.sl q hq
      rw [List.mem_singleton.mp hr]
      simp only [sslots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · rw [List.mem_singleton.mp hq, m, Mem.readW_writeW_self64]

theorem sslots_fb : ∀ q ∈ sslots, q.1 + 8 ≤ frameBytes := by
  intro q hq
  simp only [sslots, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> decide

theorem sregs_cs : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28] := by
  decide

include hH in
theorem ctHash_sct {K : Nat} (hc : PssChecks H) :
    RelCT isa (Two (SR H.D K (rsL H.D) (slL H))) (ctHash H) (Two (SR H.D K (sregs H.D) sslots)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  have hb : ∀ a : State, slA a ≤ 1024 → 8 + H.D + slA a + 1 + H.P.L ≤ nbA H a * H.P.B ∧ nbA H a * H.P.B ≤ 2048 :=
    fun a hs => by
      have hnb1 := Nat.lt_div_mul_add (a := 8 + H.D + slA a + H.P.L) (b := H.P.B) hB0
      have hnb2 := Nat.div_mul_le_self (8 + H.D + slA a + H.P.L) H.P.B
      have hnbB : ((8 + H.D + slA a + H.P.L) / H.P.B + 1) * H.P.B =
          (8 + H.D + slA a + H.P.L) / H.P.B * H.P.B + H.P.B := Nat.succ_mul _ _
      show _ ≤ ((8 + H.D + slA a + H.P.L) / H.P.B + 1) * H.P.B ∧ ((8 + H.D + slA a + H.P.L) / H.P.B + 1) * H.P.B ≤ 2048
      rw [hnbB]; omega
  have x19 : ∀ {a u : State}, SR H.D K (rsL H.D) (slL H) a u → u.gpr .x19 = off (scr a) oSt := fun h =>
    h.r (.x19, fun a => off (scr a) oSt) (by simp [rsL, sregs])
  have x21 : ∀ {a u : State}, SR H.D K (rsL H.D) (slL H) a u → u.gpr .x21 = off (scr a) oDig := fun h =>
    h.r (.x21, fun a => off (scr a) oDig) (by simp [rsL, sregs])
  have x22 : ∀ {a u : State}, SR H.D K (rsL H.D) (slL H) a u → u.gpr .x22 = BitVec.ofNat 64 (8 + H.D + slA a) :=
    fun h => h.r (.x22, fun a => BitVec.ofNat 64 (8 + H.D + slA a)) (by simp [rsL])
  have nb : ∀ {a u : State}, SR H.D K (rsL H.D) (slL H) a u →
      u.mem.readW (off (fb a) sNb) 64 = BitVec.ofNat 64 (nbA H a) := fun h =>
    h.sl (sNb, fun a => BitVec.ofNat 64 (nbA H a)) (by simp [slL])
  refine two_post (two_map (fun a => (⟨fb a, scr a, nbA H a, none⟩ : HA)) (fun a u h => {
      L := h.L
      x19 := x19 h
      x21 := x21 h
      nb := nb h
      len := ⟨8 + H.D + slA a, x22 h, (hb a h.sl_le).1⟩
      hnb := (hb a h.sl_le).2
      fx := fun _ e => nomatch e }) (ctHash_ct hH hc)) fun a u h => ?_
  have hs := h.sl_le
  refine WP.mono (ctHashWith_out hH (pad80 H) h.L (fun _ _ => rfl) (x19 h) (x21 h) (x22 h) (nb h) (hb a hs).1
    (hb a hs).2 fun L' R' h22' hNb' => ?_) fun u' O => ?_
  · exact WP.mono (pad80_ok H L' R' hlg.1 hlg.2 (by omega) (hb a hs).2 (by have := (hb a hs).1; omega) h22' hNb')
      fun _ ⟨k, f, r⟩ => ⟨k.mono, f, r⟩
  refine h.congr O.sp O.rd O.wr (O.cs .x20 (by decide)) (fun q hq => ?_) fun q hq => ?_
  · rw [O.cs q.1 (sregs_cs _ (sregs_fst hq))]; exact h.r q (List.mem_append_left _ hq)
  · rw [slot_keep O.fr fun r hr => ?_]
    · exact h.sl q (List.mem_append_left _ hq)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.L.dFS.sub_left (Offset.sub_base _ (sslots_fb q hq))
    · exact slot_not_below _ (sslots_fb q hq)

theorem clearEm_sct {D K : Nat} :
    RelCT isa (Two (SR D K (sregs D) sslots)) clearEm (Two (SR D K (sregs D) sslots)) :=
  two_post (two_taint [.x20, .x23] (SR.pins fun r hr => by
      simp at hr; rcases hr with rfl | rfl <;> simp [sregs]) (by taint_decide))
    fun a _ h => WP.mono (clearEm_ok h.L (fun _ _ => rfl) (k := kA a) (h.x23 (by simp [sregs]))
      (by have := h.ok.k1; omega) h.ok.k2) fun _ ⟨k, f, _⟩ => h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L)

/-- In `putSalt`, after `x14 := DB + dbLen` and the salt's length, and after
the `0x01` and the salt's address. -/
def rsP1 (D : Nat) : List (Reg × (State → BitVec 64)) :=
  sregs D ++ [(.x14, fun a => off (scr a) (oEm + loA a + dbA D a)), (.x12, fun a => stackArg a 10)]
def rsP2 (D : Nat) : List (Reg × (State → BitVec 64)) :=
  sregs D ++ [(.x11, fun a => stackArg a 9), (.x14, fun a => off (scr a) (oEm + loA a + dbA D a - slA a)),
    (.x12, fun a => stackArg a 10)]

theorem sl_ofNat (a : State) : stackArg a 10 = BitVec.ofNat 64 (slA a) := by
  rw [slA, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem putSalt_sct {D K : Nat} :
    RelCT isa (Two (SR D K (sregs D) sslots)) putSalt (Two (SR D K (sregs D) sslots)) := by
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  have x24 : ∀ {rs : List (Reg × (State → BitVec 64))} {a u : State}, SR D K (sregs D ++ rs) sslots a u →
      u.gpr .x24 = off (scr a) (oEm + loA a) := fun h =>
    h.r (.x24, fun a => off (scr a) (oEm + loA a)) (List.mem_append_left _ (by simp [sregs]))
  have x25 : ∀ {rs : List (Reg × (State → BitVec 64))} {a u : State}, SR D K (sregs D ++ rs) sslots a u →
      u.gpr .x25 = BitVec.ofNat 64 (dbA D a) := fun h =>
    h.r (.x25, fun a => BitVec.ofNat 64 (dbA D a)) (List.mem_append_left _ (by simp [sregs]))
  refine two_post ?_ fun a u h => ?_
  rotate_left
  · have hf := h.ok.fit; have hk2 := h.ok.k2
    have hdb : dbA D a = kA a - loA a - D - 1 := rfl
    exact WP.mono (putSalt_ok h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA D a) (q := stackArg a 9)
      (sl := slA a) (x24 (rs := []) (by rw [List.append_nil]; exact h)) (x25 (rs := []) (by rw [List.append_nil]; exact h))
      (h.sl (sSalt, fun a => stackArg a 9) (by simp [sslots]))
      ((h.sl (sSaltLen, fun a => stackArg a 10) (by simp [sslots])).trans (sl_ofNat a))
      (by omega) (by omega) h.salt.1 h.salt.2) fun _ ⟨k, f, _⟩ =>
        h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L)
  unfold putSalt
  refine RelCT.seq_block_append (M := isa) (l₁ := [.add .x .x14 .x24 .x25, ld .x12 sSaltLen]) ?_
  refine two_step (Ψ := SR D K (rsP1 D) sslots) (two_taint [] (pins_nil SR.sp) (by taint_decide))
    (fun a u h => ?_) ?_
  · have nk : ∀ q ∈ sregs D, q.1 ∉ [Reg.x14, .x12] := nk_of (by decide)
    unfold ld
    refine wp_add fun u₁ o₁ e₁ => wp_ldrSp (by decide) (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot h.L (by decide))
      fun u₂ o₂ e₂ => wp_nil ?_
    have O : Only [.x14, .x12] u u₂ := (o₁.trans o₂).mono
    refine h.congr O.sp O.rd O.wr (O.get .x20) (fun q hq => ?_) fun q hq => by rw [O.mem]; exact h.sl q hq
    rcases List.mem_append.mp hq with hq | hq
    · rw [O.get q.1 (nk q hq)]; exact h.r q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · rw [o₂.get .x14, e₁, x24 (rs := []) (by rw [List.append_nil]; exact h),
          x25 (rs := []) (by rw [List.append_nil]; exact h), off_add]
      · rw [e₂, o₁.mem, o₁.sp, h.L.sp]; exact h.sl (sSaltLen, fun a => stackArg a 10) (by simp [sslots])
  refine two_step (Ψ := SR D K (rsP2 D) sslots) (two_taint [.x12, .x14] (SR.pins fun r hr => by
      simp at hr; rcases hr with rfl | rfl <;> simp [rsP1]) (by taint_decide)) (fun a u h => ?_) ?_
  · have nk : ∀ q ∈ sregs D, q.1 ∉ [Reg.x14, .x9, .x11] := nk_of (by decide)
    have hf := h.ok.fit; have hk2 := h.ok.k2
    have hdb : dbA D a = kA a - loA a - D - 1 := rfl
    have x14 : u.gpr .x14 = off (scr a) (oEm + loA a + dbA D a) :=
      h.r (.x14, fun a => off (scr a) (oEm + loA a + dbA D a)) (by simp [rsP1])
    have x12 : u.gpr .x12 = stackArg a 10 := h.r (.x12, fun a => stackArg a 10) (by simp [rsP1])
    unfold ld
    refine wp_sub fun u₃ o₃ e₃ => wp_subImm (by decide) fun u₄ o₄ e₄ => wp_movz fun u₅ o₅ e₅ => ?_
    have h14 : u₅.gpr .x14 = off (scr a) (oEm + loA a + dbA D a - slA a - 1) := by
      rw [o₅.get .x14, e₄, e₃, x14, x12, sl_ofNat, off_sub _ (by omega), off_sub _ (by omega)]
    have O₅ : Only [.x14, .x9] u u₅ := (o₃.trans (o₄.trans o₅)).mono
    refine wp_strb (by decide) (by rw [h14, BitVec.add_zero]) (by rw [O₅.wr]; exact h.L.st (by omega))
      fun u₆ m₆ => wp_addImm (by decide) fun u₇ o₇ e₇ => wp_ldrSp (by decide)
        (by rw [o₇.sp, o₇.rd, o₇.wr, m₆.sp, m₆.rd, m₆.wr, O₅.sp, O₅.rd, O₅.wr]; exact ld_slot h.L (by decide))
        fun u₈ o₈ e₈ => wp_nil ?_
    have K : Keep [.x14, .x9, .x11] u u₈ := (O₅.keep.trans (m₆.keep.trans (o₇.keep.trans o₈.keep))).mono
    have hm : u₈.mem = u.mem.writeW (off (scr a) (oEm + loA a + dbA D a - slA a - 1)) (1 : Byte) := by
      rw [o₈.mem, o₇.mem, m₆.mem, O₅.mem, e₅]; rfl
    have hfr := wS_frame u.mem (scr a) (x := oEm + loA a + dbA D a - slA a - 1) (by omega) (1 : Byte)
    refine h.congr K.sp K.rd K.wr (K.get .x20) (fun q hq => ?_) fun q hq => ?_
    · rcases List.mem_append.mp hq with hq | hq
      · rw [K.get q.1 (nk q hq)]; exact h.r q (List.mem_append_left _ hq)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · rw [e₈, o₇.mem, m₆.mem, O₅.mem, o₇.sp, m₆.sp, O₅.sp, h.L.sp, ← O₅.mem, ← m₆.mem, ← o₇.mem, ← o₈.mem, hm,
            slot_keep hfr (h.L.slotSd (by decide))]
          exact h.sl (sSalt, fun a => stackArg a 9) (by simp [sslots])
        · rw [o₈.get .x14, e₇, m₆.gpr, h14, off_add, show oEm + loA a + dbA D a - slA a - 1 + 1 =
            oEm + loA a + dbA D a - slA a by omega]
        · rw [K.get .x12]; exact x12
    · rw [hm, slot_keep hfr (sslots_S h.L q hq)]; exact h.sl q hq
  have p12 : ∀ a s, SR D K (rsP2 D) sslots a s → s.gpr .x12 = stackArg a 10 := fun a s h =>
    h.r (.x12, fun a => stackArg a 10) (by simp [rsP2])
  exact two_ite (fun a s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, p12 a s₁ h₁, p12 a s₂ h₂])
    (two_taint [] (fun a s₁ s₂ h₁ h₂ => pins_nil SR.sp a s₁ s₂ h₁.1 h₂.1) (by taint_decide))
    (two_taint [.x11, .x12, .x14] (fun a s₁ s₂ h₁ h₂ => SR.pins (rs := rsP2 D) (fun r hr => by
      simp at hr; rcases hr with rfl | rfl | rfl <;> simp [rsP2]) a s₁ s₂ h₁.1 h₂.1) (by taint_decide))

include hH in
theorem putH_sct {K : Nat} :
    RelCT isa (Two (SR H.D K (sregs H.D) sslots)) (putH H) (Two (SR H.D K (sregs H.D) sslots)) := by
  have c1 : oEm = 2560 := rfl
  refine two_post (two_taintE [.x20, .x21, .x23, .x24, .x25] (SR.pins fun r hr => by
      simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [sregs])
    (c' := Code.eraseOff (putH zH)) rfl (by taint_decide)) fun a u h => ?_
  have hf := h.ok.fit; have hk2 := h.ok.k2
  have hdb : dbA H.D a = kA a - loA a - H.D - 1 := rfl
  exact WP.mono (putH_ok hH h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA H.D a) (k := kA a)
    (h.r (.x24, fun a => off (scr a) (oEm + loA a)) (by simp [sregs]))
    (h.r (.x25, fun a => BitVec.ofNat 64 (dbA H.D a)) (by simp [sregs]))
    (h.r (.x21, fun a => off (scr a) oDig) (by simp [sregs])) (h.x23 (by simp [sregs])) (by omega) (by omega) hk2)
    fun _ ⟨k, f, _⟩ => h.keep k (nk_of (by decide)) (by decide) f (sslots_S h.L)

/-- After `mgfXor`: `DB`'s place. -/
def rsT : List (Reg × (State → BitVec 64)) := [(.x24, fun a => off (scr a) (oEm + loA a))]

include hH in
theorem mgfXor_sct {K : Nat} {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) (hc : PssChecks H) :
    RelCT isa (Two (SR H.D K (sregs H.D) sslots)) (mgfXor H) (Two (SR H.D K rsT [])) := by
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have hd : ∀ a : State, SOk H.D a → DbAt H.D (oEm + loA a) (dbA H.D a) := fun a ok => by
    have hf := ok.fit; have hk2 := ok.k2
    have hdb : dbA H.D a = kA a - loA a - H.D - 1 := rfl
    exact ⟨by omega, by omega, by omega⟩
  have g : ∀ {a u : State}, SR H.D K (sregs H.D) sslots a u → u.gpr .x19 = off (scr a) oSt ∧
      u.gpr .x21 = off (scr a) oDig ∧ u.gpr .x24 = off (scr a) (oEm + loA a) ∧
      u.gpr .x25 = BitVec.ofNat 64 (dbA H.D a) := fun h =>
    ⟨h.r (.x19, fun a => off (scr a) oSt) (by simp [sregs]), h.r (.x21, fun a => off (scr a) oDig) (by simp [sregs]),
      h.r (.x24, fun a => off (scr a) (oEm + loA a)) (by simp [sregs]),
      h.r (.x25, fun a => BitVec.ofNat 64 (dbA H.D a)) (by simp [sregs])⟩
  refine two_post (two_map (fun a => (⟨fb a, scr a, oEm + loA a, dbA H.D a⟩ : MA))
    (fun a u h => ⟨h.L, hd a h.ok, (g h).1, (g h).2.1, (g h).2.2.1, (g h).2.2.2⟩) (mgfXor_ct hH hGh hGl hG hc))
    fun a u h => WP.mono (mgfXor_ok hH hGh hGl hG h.L (fun _ _ => rfl) (hd a h.ok) (g h).1 (g h).2.1 (g h).2.2.1
      (g h).2.2.2) fun u' ⟨sp, rd, wr, cs, _⟩ => h.congr sp rd wr (cs .x20 (by decide)) (fun q hq => ?_)
        fun _ h => absurd h List.not_mem_nil
  rw [List.mem_singleton.mp hq]
  exact (cs .x24 (by decide)).trans (g h).2.2.1

theorem clearTop_sct {D K : Nat} : RelCT isa (Two (SR D K rsT [])) (.block clearTop) fun _ _ => True :=
  two_taint [.x24] (SR.pins fun r hr => by simp at hr; subst hr; simp [rsT]) (by taint_decide)

/-- The encoding is constant time. -/
theorem signEnc_ct {K : Nat} {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) (hc : PssChecks H) :
    RelCT isa (Two (SR H.D K (sregs0 H.D) sslots)) (signEnc H) fun _ _ => True := by
  unfold signEnc seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  exact RelCT.seq dbRegs_sct (RelCT.seq clearY_sct (RelCT.seq (copyDigest_sct hH) (RelCT.seq (copySaltY_sct hH)
    (RelCT.seq (signLen_sct hH) (RelCT.seq (ctHash_sct hH hc) (RelCT.seq clearEm_sct (RelCT.seq putSalt_sct
      (RelCT.seq (putH_sct hH) (RelCT.seq (mgfXor_sct hH hGh hGl hG hc) clearTop_sct)))))))))

end

end VG.Proof.RsaPss.AArch64.Sgn
