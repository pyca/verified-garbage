import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPss.AArch64.CtPadEq

/-!
# RSASSA-PSS on AArch64: hashing a message of secret length

`ctHashWith padding` leaves the digest of the first `ℓ` bytes of `Y` at
`scratch + oDig` (`ctHashWith_ok`), from a state where those bytes are
followed by zeros up to `nbm` blocks, for a padding step that ORs `0x80`
into byte `ℓ` (`pad80` or `fixedPad80`). It keeps everything but our part
of the working space before `oEm` and from `oY` on.
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_addImm)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MdStream (Md)
open VG.Proof.RsaPss (padded lastBlk pad_getD pad_length)

theorem bytesAt_writeBytes_take (m : Mem) (q : Addr) (xs : List Byte) {d : Nat} (hd : d ≤ xs.length)
    (hl : xs.length < 2 ^ 64) : Spec.Rsa.bytesAt (writeBytes m q xs) q d = xs.take d := by
  conv_rhs => rw [← VG.Proof.RsaPkcs1Sig.bytesAt_writeBytes m q xs hl]
  simp only [Spec.Rsa.bytesAt]
  rw [← List.map_take, List.take_range, Nat.min_eq_left hd]

/-- What `ctHash` keeps of the state `t`. -/
structure CtOut (t : State) (F S : Addr) (V : Nat → Byte) (t' : State) : Prop where
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  cs : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28], t'.gpr r = t.gpr r
  vec : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  fr : Frame [⟨S, oRsa⟩, below F 16] t.mem t'.mem
  em : ∀ o, oEm ≤ o → o < oY → t'.mem (off S o) = V o

/-- A slot of the frame is not on the stack below it. -/
theorem slot_not_below (F : Addr) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Disjoint ⟨off F d, n⟩ (below F 16) := by
  have e : off F d = (F - BitVec.ofNat 64 16) + BitVec.ofNat 64 (16 + d) := by
    rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have := Offset.disjoint (F - BitVec.ofNat 64 16) (d := 16 + d) (n := n) (e := 0) (k := 16) (Or.inr (by omega_arith))
    (by unfold frameBytes at h; omega_arith) (by omega_arith)
  have z : BitVec.ofNat 64 0 = 0#64 := rfl
  rw [z, BitVec.add_zero, ← e] at this
  exact this

/-- The block count in its slot, kept by writes elsewhere. -/
theorem nb_keep {F : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨off F sNb, 8⟩ r) :
    m'.readW (off F sNb) 64 = m.readW (off F sNb) 64 :=
  hf.readW (r := ⟨off F sNb, 8⟩) (Region.contains_self _ _) hd (by decide)

theorem Lay.nbS {t : State} {F S : Addr} (L : Lay t F S) :
    ∀ r ∈ [(⟨S, oRsa⟩ : Region)], Region.Disjoint ⟨off F sNb, 8⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact L.dFS.sub_left (Offset.sub_base F (by decide))

theorem Frame.wide {S F : Addr} {m m' : Mem} (h : Frame [⟨S, oRsa⟩] m m') :
    Frame [⟨S, oRsa⟩, below F 16] m m' :=
  h.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self

/-- The padding step of `ctHashWith`: `0x80` ORed into byte `ℓ` of `Y`. -/
def PadOk (H : Hash) (padding : Prog isa) (F S : Addr) (ℓ nbm : Nat) : Prop :=
  ∀ {u : State} {V : Nat → Byte}, Lay u F S → Rep u.mem S V → u.gpr .x22 = BitVec.ofNat 64 ℓ →
    u.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm →
    WP isa padding u fun u' => Keep [.x9, .x10, .x11, .x12, .x13, .x14] u u' ∧
      Frame [⟨S, oRsa⟩] u.mem u'.mem ∧ Rep u'.mem S (v80 V ℓ (nbm * H.P.B))

section
variable {H : Hash} (hH : HashOK H)

theorem stateAt_rep {m m' : Mem} {S : Addr} {V V' : Nat → Byte} (R : Rep m S V) (R' : Rep m' S V') {o : Nat}
    (ho : o + H.P.N ≤ oRsa) (h : ∀ i < H.P.N, V' (o + i) = V (o + i)) :
    hH.md.stateAt m' (off S o) = hH.md.stateAt m (off S o) :=
  hH.md.stateAt_congr fun i hi => by rw [off_add, R' _ (by omega_arith), R _ (by omega_arith), h i hi]

/-- The streaming `init` on `scratch + oSt`. -/
theorem ctInit_ok {t : State} {F S : Addr} (L : Lay t F S) (h19 : t.gpr .x19 = off S oSt) :
    WP isa (ctInit H) t fun u => u.sp = t.sp ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) ∧
      Frame [⟨off S oSt, H.P.N + H.P.B⟩, below F 16] t.mem u.mem ∧
      hH.md.stateAt u.mem (off S oSt) = hH.iv := by
  have hN := hH.N_le; have hBl := hH.B_le
  unfold ctInit
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_nil ?_)
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.init_call hH.stream (st := off S oSt) (by rw [e₁, h19])
    (by rw [o₁.wr]; exact Covers.one (L.st (n := H.P.N + H.P.B) (by unfold oSt oRsa; omega_arith))) fun u hA hr => ?_
  refine ⟨by rw [hA.sp, o₁.sp], by rw [hA.rd, o₁.rd], by rw [hA.wr, o₁.wr], fun r hr h30 => ?_,
    fun r hr => by rw [hA.vec r hr, o₁.vcs r hr], ?_, ?_⟩
  · rw [hA.cs r hr h30, o₁.gpr r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide)]
  · have := hA.frame
    rw [o₁.mem, o₁.sp, L.sp] at this
    exact this
  · obtain ⟨h1, -⟩ := (hH.repr _ _ _).1 hr
    rw [h1, List.length_nil, Nat.zero_div, Md.compressList_zero]

/-- The digest of the hash value at `scratch + oSel` to `scratch + oDig`. -/
theorem digestOut_ok {t : State} {F S : Addr} (L : Lay t F S) (h21 : t.gpr .x21 = off S oDig) :
    WP isa (.block (digestOut H)) t fun t' => Keep [.x19, .x9] t t' ∧ t'.gpr .x19 = off S oSt ∧
      t'.mem = writeBytes t.mem (off S oDig) (hH.md.digest (hH.md.stateAt t.mem (off S oSel))) := by
  have hN := hH.N_le
  unfold digestOut
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => ?_
  show WP isa (.block (H.P.out ++ [.addImm .x .x19 .x20 oSt])) u₁ _
  rw [WP.block_append_iff]
  have h19 : u₁.gpr .x19 = off S oSel := by rw [e₁, L.x20]
  have r19 : InRegions (u₁.rd ++ u₁.wr) (u₁.gpr .x19) H.P.N := by
    rw [h19, o₁.rd, o₁.wr]; exact L.ld (by unfold oSel oRsa; omega_arith)
  have w21 : InRegions u₁.wr (u₁.gpr .x21) H.P.N := by
    rw [o₁.get .x21, h21, o₁.wr]; exact L.st (by unfold oDig oRsa; omega_arith)
  have d : Region.Disjoint ⟨u₁.gpr .x19, H.P.N⟩ ⟨u₁.gpr .x21, H.P.N⟩ := by
    rw [h19, o₁.get .x21, h21]
    exact Offset.disjoint _ (by unfold oSel oDig; omega_arith) (by unfold oSel; omega_arith) (by unfold oDig; omega_arith)
  refine WP.mono (WP.preservedV (hH.shape.out u₁ r19 w21 d)
      (by rw [Code.allInstrs_eq]; exact hH.shape.outKeepsV))
    fun u₂ ⟨⟨hg, hrd, hwr, hsp, hm⟩, hv⟩ => ?_
  refine wp_addImm (by decide) fun u₃ o₃ e₃ => wp_nil ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr => ?_⟩, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [o₃.gpr r (by simpa using hr.1), hg r hr.2, o₁.gpr r (by simpa using hr.1)]
  · rw [o₃.rd, hrd, o₁.rd]
  · rw [o₃.wr, hwr, o₁.wr]
  · rw [o₃.sp, hsp, o₁.sp]
  · rw [o₃.vcs r hr, hv r hr, o₁.vcs r hr]
  · rw [e₃, hg .x20 (by decide), o₁.get .x20, L.x20]
  · rw [o₃.mem, hm, h19, o₁.get .x21, h21, o₁.mem]

theorem ctHashWith_ok (padding : Prog isa) {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte}
    (R : Rep t.mem S V) {msg : List Byte} {nbm : Nat} (h19 : t.gpr .x19 = off S oSt)
    (h21 : t.gpr .x21 = off S oDig) (h22 : t.gpr .x22 = BitVec.ofNat 64 msg.length)
    (hNb : t.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm)
    (hfit : msg.length + 1 + H.P.L ≤ nbm * H.P.B) (hnb : nbm * H.P.B ≤ 2048)
    (hY : ∀ i < nbm * H.P.B, V (oY + i) = msg.getD i 0) (hp : PadOk H padding F S msg.length nbm) :
    WP isa (ctHashWith H padding) t fun t' => CtOut t F S V t' ∧
      Spec.Rsa.bytesAt t'.mem (off S oDig) H.D = hH.SH.H.hash msg := by
  have hB := hH.B_le
  have hB0 := hH.B_pos
  have hN := hH.N_le
  have hd := hH.sizes.dims
  have hNL := hH.sizes.NL
  have hDN := hH.sizes.DN
  have hso : H.P.so ≤ 1024 := hd.so.2
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  have hLB : H.P.L < H.P.B := by have : 0 < H.P.N := hd.N.1; omega_arith
  have c1 : oY = 3584 := rfl
  have c2 : oLen = 2368 := rfl
  have c3 : oDig = 2304 := rfl
  have c4 : oSt = 2048 := rfl
  have c5 : oSel = 2240 := rfl
  have c6 : oRsa = 8192 := rfl
  have c7 : oEm = 2560 := rfl
  have hfb : (msg.length + H.P.L) / H.P.B < nbm := (Nat.div_lt_iff_lt_mul hB0).mpr (by omega_arith)
  have hnbm : 0 < nbm := by rcases Nat.eq_zero_or_pos nbm with h | h <;> [subst h; exact h]; omega_arith
  have hfbB : H.P.B * ((msg.length + H.P.L) / H.P.B + 1) ≤ nbm * H.P.B := by
    rw [Nat.mul_comm nbm]; exact Nat.mul_le_mul_left _ hfb
  unfold ctHashWith seqs seqs seqs seqs seqs
  -- `init`.
  refine WP.seq (WP.mono (ctInit_ok hH L h19) fun u1 ⟨sp1, rd1, wr1, cs1, v1, fr1, iv1⟩ => ?_)
  have g1 : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28], u1.gpr r = t.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact cs1 _ (by decide) (by decide)
  have L1 : Lay u1 F S := L.congr sp1 wr1 (g1 .x20 (by decide))
  have m1 : ∀ o < oRsa, ¬ (oSt ≤ o ∧ o < oSt + (H.P.N + H.P.B)) → u1.mem (off S o) = V o := by
    intro o ho hno
    rw [← R o ho]
    refine fr1 _ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact not_in S (by omega_arith) (by omega_arith) (by omega_arith)
    · exact fun hc => L.dB _ hc (Offset.contains_base S (by omega_arith) (by omega_arith))
  have hNb1 : u1.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by
    rw [nb_keep fr1 fun r hr => ?_]; exact hNb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (L.dFS.sub_left (Offset.sub_base F (by decide))).sub_right (Offset.sub_base S (by omega_arith))
    · exact slot_not_below F (by decide)
  have R1 : Rep u1.mem S (fun o => u1.mem (off S o)) := fun _ _ => rfl
  have x22₁ : u1.gpr .x22 = BitVec.ofNat 64 msg.length := by rw [g1 .x22 (by decide), h22]
  -- `0x80`.
  refine WP.seq (WP.mono (hp L1 R1 x22₁ hNb1) fun u2 ⟨k2, fr2, R2⟩ => ?_)
  have L2 : Lay u2 F S := L1.congr k2.sp k2.wr (k2.get .x20)
  have hNb2 : u2.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by rw [nb_keep fr2 L.nbS]; exact hNb1
  have x22₂ : u2.gpr .x22 = BitVec.ofNat 64 msg.length := by rw [k2.get .x22]; exact x22₁
  -- The length field.
  refine WP.seq (WP.mono (lenField_ok H hH.shape L2 R2 (by omega_arith) hd.L.2) fun u3 ⟨k3, h19₃, fr3, R3⟩ => ?_)
  rw [x22₂, hH.md.lenOf_eq _ (hH.lenOk _ (by omega_arith))] at R3
  have L3 : Lay u3 F S := L2.congr k3.sp k3.wr (k3.get .x20)
  have hNb3 : u3.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by rw [nb_keep fr3 L.nbS]; exact hNb2
  have x22₃ : u3.gpr .x22 = BitVec.ofNat 64 msg.length := by rw [k3.get .x22]; exact x22₂
  -- Into the last block.
  refine WP.seq (WP.mono (lenLoop_ok H L3 R3 hlg.1 hlg.2 (by omega_arith) hd.L.1 hd.L.2 hB (by omega_arith)
    hnb hfb x22₃ hNb3) fun u4 ⟨k4, fr4, R4⟩ => ?_)
  have L4 : Lay u4 F S := L3.congr k4.sp k4.wr (k4.get .x20)
  have hNb4 : u4.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by rw [nb_keep fr4 L.nbS]; exact hNb3
  have x22₄ : u4.gpr .x22 = BitVec.ofNat 64 msg.length := by rw [k4.get .x22]; exact x22₃
  have x19₄ : u4.gpr .x19 = off S oSt := by rw [k4.get .x19]; exact h19₃
  have iv4 : hH.md.stateAt u4.mem (off S oSt) = hH.iv := by
    rw [stateAt_rep hH R1 R4 (by omega_arith) fun i hi => ?_, iv1]
    simp (disch := omega_arith) only [LenLoop.vLen, updL, v80, ite_eq_right]
  -- Every block.
  refine WP.seq (WP.mono (compLoop_ok hH L4 R4 hlg.1 hlg.2 (by omega_arith) hnb hnbm x22₄ x19₄
    hNb4) fun u5 C => ?_)
  have L5 : Lay u5 F S := L4.congr C.sp C.wr (C.cs .x20 (by decide))
  -- The digest.
  refine WP.mono (digestOut_ok hH L5 (by rw [C.cs .x21 (by decide), k4.get .x21, k3.get .x21, k2.get .x21,
    g1 .x21 (by decide), h21])) fun u6 ⟨k6, h19₆, m6⟩ => ?_
  have hdl := hH.md.digest_length (hH.md.stateAt u5.mem (off S oSel))
  have hsel := C.sel hfb
  rw [iv4] at hsel
  refine ⟨⟨k6.sp.trans (C.sp.trans (k4.sp.trans (k3.sp.trans (k2.sp.trans sp1)))),
    k6.rd.trans (C.rd.trans (k4.rd.trans (k3.rd.trans (k2.rd.trans rd1)))),
    k6.wr.trans (C.wr.trans (k4.wr.trans (k3.wr.trans (k2.wr.trans wr1)))), fun r hr => ?_,
    fun r hr => (k6.vcs r hr).trans ((C.vec r hr).trans ((k4.vcs r hr).trans ((k3.vcs r hr).trans
      ((k2.vcs r hr).trans (v1 r hr))))), ?_, fun o ho₁ ho₂ => ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h19₆, h19]
    all_goals rw [k6.get _ (by decide), C.cs _ (by decide), k4.get _ (by decide), k3.get _ (by decide),
      k2.get _ (by decide), g1 _ (by decide)]
  · have F1 : Frame [⟨S, oRsa⟩, below F 16] t.mem u1.mem := fr1.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub_base S (by omega_arith)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    have F6 : Frame [⟨S, oRsa⟩] u5.mem u6.mem := by
      rw [m6]; exact writeBytes_frame _ _ _ (Offset.contains_base S (by omega_arith) (by omega_arith))
    exact F1.trans ((Frame.wide fr2).trans ((Frame.wide fr3).trans ((Frame.wide fr4).trans
      ((Frame.wide C.fr).trans (Frame.wide F6)))))
  · have R6 := (show Rep u5.mem S (fun o => u5.mem (off S o)) from fun _ _ => rfl).writeBytes
      (o := oDig) (xs := hH.md.digest (hH.md.stateAt u5.mem (off S oSel))) (by omega_arith)
    rw [m6, R6 o (by omega_arith)]
    simp (disch := omega_arith) only [updL, ite_eq_right]
    rw [C.keep o (by omega_arith) (by unfold CompW; omega_arith), ← m1 o (by omega_arith) (by omega_arith)]
    simp (disch := omega_arith) only [LenLoop.vLen, updL, v80, hH.md.lenBytes_length, ite_eq_right]
  · rw [m6, bytesAt_writeBytes_take _ _ _ (by omega_arith) (by omega_arith), hsel, hH.hash, MdStream.Md.hash,
      RsaPss.pad_length hH.md msg hB0 hLB, Nat.mul_div_cancel_left _ hB0]
    refine congrArg (fun x => (hH.md.digest x).take H.D) (hH.md.compressList_congr fun j hj => ?_)
    rw [yList_getD (by omega_arith), RsaPss.pad_getD hH.md msg hB0 hLB hj]
    refine ypad hB0 hLB hd.L.2 (hH.md.lenBytes_length _) hnb (by omega_arith) (fun i hi => ?_) j hj (by omega_arith)
    rw [m1 _ (by omega_arith) (by omega_arith), hY i hi]
    by_cases h : i < msg.length
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega_arith)]; rfl

include hH in
/-- `ctHashWith`'s frame, registers and `EM`, for any message in `Y`. -/
theorem ctHashWith_out (padding : Prog isa) {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte}
    (R : Rep t.mem S V) {ℓ nbm : Nat} (h19 : t.gpr .x19 = off S oSt)
    (h21 : t.gpr .x21 = off S oDig) (h22 : t.gpr .x22 = BitVec.ofNat 64 ℓ)
    (hNb : t.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm)
    (hfit : ℓ + 1 + H.P.L ≤ nbm * H.P.B) (hnb : nbm * H.P.B ≤ 2048) (hp : PadOk H padding F S ℓ nbm) :
    WP isa (ctHashWith H padding) t (CtOut t F S V) := by
  have hB := hH.B_le
  have hB0 := hH.B_pos
  have hN := hH.N_le
  have hd := hH.sizes.dims
  have hNL := hH.sizes.NL
  have hDN := hH.sizes.DN
  have hso : H.P.so ≤ 1024 := hd.so.2
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  have hLB : H.P.L < H.P.B := by have : 0 < H.P.N := hd.N.1; omega_arith
  have c1 : oY = 3584 := rfl
  have c2 : oLen = 2368 := rfl
  have c3 : oDig = 2304 := rfl
  have c4 : oSt = 2048 := rfl
  have c5 : oSel = 2240 := rfl
  have c6 : oRsa = 8192 := rfl
  have c7 : oEm = 2560 := rfl
  have hfb : (ℓ + H.P.L) / H.P.B < nbm := (Nat.div_lt_iff_lt_mul hB0).mpr (by omega_arith)
  have hnbm : 0 < nbm := by rcases Nat.eq_zero_or_pos nbm with h | h <;> [subst h; exact h]; omega_arith
  have hfbB : H.P.B * ((ℓ + H.P.L) / H.P.B + 1) ≤ nbm * H.P.B := by
    rw [Nat.mul_comm nbm]; exact Nat.mul_le_mul_left _ hfb
  unfold ctHashWith seqs seqs seqs seqs seqs
  -- `init`.
  refine WP.seq (WP.mono (ctInit_ok hH L h19) fun u1 ⟨sp1, rd1, wr1, cs1, v1, fr1, iv1⟩ => ?_)
  have g1 : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28], u1.gpr r = t.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact cs1 _ (by decide) (by decide)
  have L1 : Lay u1 F S := L.congr sp1 wr1 (g1 .x20 (by decide))
  have m1 : ∀ o < oRsa, ¬ (oSt ≤ o ∧ o < oSt + (H.P.N + H.P.B)) → u1.mem (off S o) = V o := by
    intro o ho hno
    rw [← R o ho]
    refine fr1 _ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact not_in S (by omega_arith) (by omega_arith) (by omega_arith)
    · exact fun hc => L.dB _ hc (Offset.contains_base S (by omega_arith) (by omega_arith))
  have hNb1 : u1.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by
    rw [nb_keep fr1 fun r hr => ?_]; exact hNb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (L.dFS.sub_left (Offset.sub_base F (by decide))).sub_right (Offset.sub_base S (by omega_arith))
    · exact slot_not_below F (by decide)
  have R1 : Rep u1.mem S (fun o => u1.mem (off S o)) := fun _ _ => rfl
  have x22₁ : u1.gpr .x22 = BitVec.ofNat 64 ℓ := by rw [g1 .x22 (by decide), h22]
  -- `0x80`.
  refine WP.seq (WP.mono (hp L1 R1 x22₁ hNb1) fun u2 ⟨k2, fr2, R2⟩ => ?_)
  have L2 : Lay u2 F S := L1.congr k2.sp k2.wr (k2.get .x20)
  have hNb2 : u2.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by rw [nb_keep fr2 L.nbS]; exact hNb1
  have x22₂ : u2.gpr .x22 = BitVec.ofNat 64 ℓ := by rw [k2.get .x22]; exact x22₁
  -- The length field.
  refine WP.seq (WP.mono (lenField_ok H hH.shape L2 R2 (by omega_arith) hd.L.2) fun u3 ⟨k3, h19₃, fr3, R3⟩ => ?_)
  rw [x22₂, hH.md.lenOf_eq _ (hH.lenOk _ (by omega_arith))] at R3
  have L3 : Lay u3 F S := L2.congr k3.sp k3.wr (k3.get .x20)
  have hNb3 : u3.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by rw [nb_keep fr3 L.nbS]; exact hNb2
  have x22₃ : u3.gpr .x22 = BitVec.ofNat 64 ℓ := by rw [k3.get .x22]; exact x22₂
  -- Into the last block.
  refine WP.seq (WP.mono (lenLoop_ok H L3 R3 hlg.1 hlg.2 (by omega_arith) hd.L.1 hd.L.2 hB (by omega_arith)
    hnb hfb x22₃ hNb3) fun u4 ⟨k4, fr4, R4⟩ => ?_)
  have L4 : Lay u4 F S := L3.congr k4.sp k4.wr (k4.get .x20)
  have hNb4 : u4.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by rw [nb_keep fr4 L.nbS]; exact hNb3
  have x22₄ : u4.gpr .x22 = BitVec.ofNat 64 ℓ := by rw [k4.get .x22]; exact x22₃
  have x19₄ : u4.gpr .x19 = off S oSt := by rw [k4.get .x19]; exact h19₃
  have iv4 : hH.md.stateAt u4.mem (off S oSt) = hH.iv := by
    rw [stateAt_rep hH R1 R4 (by omega_arith) fun i hi => ?_, iv1]
    simp (disch := omega_arith) only [LenLoop.vLen, updL, v80, ite_eq_right]
  -- Every block.
  refine WP.seq (WP.mono (compLoop_ok hH L4 R4 hlg.1 hlg.2 (by omega_arith) hnb hnbm x22₄ x19₄
    hNb4) fun u5 C => ?_)
  have L5 : Lay u5 F S := L4.congr C.sp C.wr (C.cs .x20 (by decide))
  -- The digest.
  refine WP.mono (digestOut_ok hH L5 (by rw [C.cs .x21 (by decide), k4.get .x21, k3.get .x21, k2.get .x21,
    g1 .x21 (by decide), h21])) fun u6 ⟨k6, h19₆, m6⟩ => ?_
  have hdl := hH.md.digest_length (hH.md.stateAt u5.mem (off S oSel))
  refine ⟨k6.sp.trans (C.sp.trans (k4.sp.trans (k3.sp.trans (k2.sp.trans sp1)))),
    k6.rd.trans (C.rd.trans (k4.rd.trans (k3.rd.trans (k2.rd.trans rd1)))),
    k6.wr.trans (C.wr.trans (k4.wr.trans (k3.wr.trans (k2.wr.trans wr1)))), fun r hr => ?_,
    fun r hr => (k6.vcs r hr).trans ((C.vec r hr).trans ((k4.vcs r hr).trans ((k3.vcs r hr).trans
      ((k2.vcs r hr).trans (v1 r hr))))), ?_, fun o ho₁ ho₂ => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h19₆, h19]
    all_goals rw [k6.get _ (by decide), C.cs _ (by decide), k4.get _ (by decide), k3.get _ (by decide),
      k2.get _ (by decide), g1 _ (by decide)]
  · have F1 : Frame [⟨S, oRsa⟩, below F 16] t.mem u1.mem := fr1.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub_base S (by omega_arith)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    have F6 : Frame [⟨S, oRsa⟩] u5.mem u6.mem := by
      rw [m6]; exact writeBytes_frame _ _ _ (Offset.contains_base S (by omega_arith) (by omega_arith))
    exact F1.trans ((Frame.wide fr2).trans ((Frame.wide fr3).trans ((Frame.wide fr4).trans
      ((Frame.wide C.fr).trans (Frame.wide F6)))))
  · have R6 := (show Rep u5.mem S (fun o => u5.mem (off S o)) from fun _ _ => rfl).writeBytes
      (o := oDig) (xs := hH.md.digest (hH.md.stateAt u5.mem (off S oSel))) (by omega_arith)
    rw [m6, R6 o (by omega_arith)]
    simp (disch := omega_arith) only [updL, ite_eq_right]
    rw [C.keep o (by omega_arith) (by unfold CompW; omega_arith), ← m1 o (by omega_arith) (by omega_arith)]
    simp (disch := omega_arith) only [LenLoop.vLen, updL, v80, hH.md.lenBytes_length, ite_eq_right]

theorem ctHash_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte}
    (R : Rep t.mem S V) {msg : List Byte} {nbm : Nat} (h19 : t.gpr .x19 = off S oSt)
    (h21 : t.gpr .x21 = off S oDig) (h22 : t.gpr .x22 = BitVec.ofNat 64 msg.length)
    (hNb : t.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm)
    (hfit : msg.length + 1 + H.P.L ≤ nbm * H.P.B) (hnb : nbm * H.P.B ≤ 2048)
    (hY : ∀ i < nbm * H.P.B, V (oY + i) = msg.getD i 0) :
    WP isa (ctHash H) t fun t' => CtOut t F S V t' ∧
      Spec.Rsa.bytesAt t'.mem (off S oDig) H.D = hH.SH.H.hash msg := by
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  refine ctHashWith_ok hH (pad80 H) L R h19 h21 h22 hNb hfit hnb hY fun L' R' h22' hNb' => ?_
  exact WP.mono (pad80_ok H L' R' hlg.1 hlg.2 (by omega_arith) hnb (by omega_arith) h22' hNb') fun _ ⟨k, f, r⟩ =>
    ⟨k.mono, f, r⟩

theorem mgfHash_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte}
    (R : Rep t.mem S V) {msg : List Byte} {nbm : Nat} (hml : msg.length = H.D + 4) (h19 : t.gpr .x19 = off S oSt)
    (h21 : t.gpr .x21 = off S oDig) (h22 : t.gpr .x22 = BitVec.ofNat 64 msg.length)
    (hNb : t.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm)
    (hfit : msg.length + 1 + H.P.L ≤ nbm * H.P.B) (hnb : nbm * H.P.B ≤ 2048)
    (hY : ∀ i < nbm * H.P.B, V (oY + i) = msg.getD i 0) :
    WP isa (mgfHash H) t fun t' => CtOut t F S V t' ∧
      Spec.Rsa.bytesAt t'.mem (off S oDig) H.D = hH.SH.H.hash msg := by
  have := hH.sizes.DN
  have := hH.N_le
  refine ctHashWith_ok hH _ L R h19 h21 h22 hNb hfit hnb hY fun L' R' _ _ => ?_
  rw [hml]
  exact WP.mono (fixedPad_ok L' R' (n := nbm * H.P.B) (by omega_arith) (by unfold oY; omega_arith)) fun _ ⟨k, f, r⟩ =>
    ⟨k.mono, f, r⟩

end

end VG.Proof.RsaPss.AArch64
