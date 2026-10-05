import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecKdk

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: IRPRF

The message of block `i` (`msgCL_run`, `msgAM_run`), one block (`prf_step`),
and the loops (`clLoop_step`, `amLoop_step`): `CL = IRPRF(KDK, "length", 256)`
at `scratch + sCL` and `AM = IRPRF(KDK, "message", k)` at `scratch + sAM`.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

/-- The message of block `i` of `CL`. -/
def msgCL (i : Nat) : List Byte :=
  Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "length" ++ Spec.Rsa.i2osp (8 * 256) 2

theorem msgCL_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {i : Nat} (hi : i < 256) (hdi : t.gpr .rdi = sc s) (hax : t.gpr .rax = BitVec.ofNat 64 i) :
    WP isa (.block (msgBytes lengthLabel clLen)) t fun t' => Outside (sc s) sMsg 16 t.mem t'.mem ∧
      Spec.Rsa.bytesAt t'.mem (scA s sMsg) 10 = msgCL i ∧ Keep [.rdx] t t' := by
  have hs := hc.scr hp
  refine (WP.keep [.rdx] (c := .block (msgBytes lengthLabel clLen)) (Q := fun t' =>
    Outside (sc s) sMsg 16 t.mem t'.mem ∧ Spec.Rsa.bytesAt t'.mem (scA s sMsg) 10 = msgCL i) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  have hst : ∀ d, d + 1 ≤ scrBytes → InRegions t.wr (off (sc s) d) 1 := fun d h => hs.st8 h
  simp only [msgBytes, lengthLabel, clLen, putByte, List.zipIdx, List.flatMap, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil, Nat.reduceAdd, sMsg]
  xrun [ea_atd (p := sc s), hdi, hax, hst 1024 (by decide), hst 1025 (by decide), hst 1026 (by decide), hst 1027 (by decide), hst 1028 (by decide), hst 1029 (by decide), hst 1030 (by decide), hst 1031 (by decide), hst 1032 (by decide), hst 1033 (by decide)]
  refine ⟨?_, ?_⟩
  · repeat (first | exact Outside.refl _ _ _ _ | refine Outside.wb ?_ _ (by decide) (by decide) (by decide))
  · simp only [Spec.Rsa.bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, scA, off_add,
      Nat.reduceAdd]
    simp (disch := decide) only [byte_wb, byte_wb_self]
    simp only [msgCL, i2osp_two, Spec.RsaPkcs1Enc.ascii, Nat.div_eq_of_lt hi]
    rw [show BitVec.setWidth 8 (BitVec.ofNat 64 i) = BitVec.ofNat 8 i from
      BitVec.eq_of_toNat_eq (by simp)]
    rfl


/-- The message of block `i` of `AM`, for a modulus of `k` bytes. -/
def msgAM (k i : Nat) : List Byte :=
  Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "message" ++ Spec.Rsa.i2osp (8 * k) 2

theorem msgAM_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {i : Nat} (hi : i < 256) (hdi : t.gpr .rdi = sc s) (hax : t.gpr .rax = BitVec.ofNat 64 i)
    (h9 : t.gpr .r9 = s.gpr .r8) :
    WP isa (.block (msgBytes messageLabel amLen)) t fun t' => Outside (sc s) sMsg 16 t.mem t'.mem ∧
      Spec.Rsa.bytesAt t'.mem (scA s sMsg) 11 = msgAM (kOf s) i ∧ Keep [.rdx] t t' := by
  have hs := hc.scr hp
  have hf := hc.frm hp
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  refine (WP.keep [.rdx] (c := .block (msgBytes messageLabel amLen)) (Q := fun t' =>
    Outside (sc s) sMsg 16 t.mem t'.mem ∧ Spec.Rsa.bytesAt t'.mem (scA s sMsg) 11 = msgAM (kOf s) i) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  have hst : ∀ d, d + 1 ≤ scrBytes → InRegions t.wr (off (sc s) d) 1 := fun d h => hs.st8 h
  simp only [msgBytes, messageLabel, amLen, putByte, List.zipIdx, List.flatMap, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil, Nat.reduceAdd, sMsg]
  xrun [ea_atd (p := sc s), hdi, hax, h9, hst 1024 (by decide), hst 1025 (by decide), hst 1026 (by decide), hst 1027 (by decide), hst 1028 (by decide), hst 1029 (by decide), hst 1030 (by decide), hst 1031 (by decide), hst 1032 (by decide), hst 1033 (by decide), hst 1034 (by decide)]
  refine ⟨?_, ?_⟩
  · repeat (first | exact Outside.refl _ _ _ _ | refine Outside.wb ?_ _ (by decide) (by decide) (by decide))
  · simp only [Spec.Rsa.bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, scA, off_add,
      Nat.reduceAdd]
    simp (disch := decide) only [byte_wb, byte_wb_self]
    simp only [msgAM, i2osp_two, Spec.RsaPkcs1Enc.ascii, Nat.div_eq_of_lt hi]
    have hx : (s.gpr .r8).toNat = kOf s := rfl
    rw [show BitVec.setWidth 8 (BitVec.ofNat 64 i) = BitVec.ofNat 8 i from BitVec.eq_of_toNat_eq (by simp),
      show BitVec.setWidth 8 ((s.gpr .r8 + s.gpr .r8 + (s.gpr .r8 + s.gpr .r8) +
          (s.gpr .r8 + s.gpr .r8 + (s.gpr .r8 + s.gpr .r8))) >>> 8) = BitVec.ofNat 8 (8 * kOf s / 256) from
        BitVec.eq_of_toNat_eq (by
          simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.shiftRight_eq_div_pow, hx]; omega),
      show BitVec.setWidth 8 (s.gpr .r8 + s.gpr .r8 + (s.gpr .r8 + s.gpr .r8) +
          (s.gpr .r8 + s.gpr .r8 + (s.gpr .r8 + s.gpr .r8))) = BitVec.ofNat 8 (8 * kOf s) from
        BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, hx]; omega)]
    rfl


/-! ## `scratch` and the slots -/

theorem KeepHi.widen {s : State} {lo lo' : List (Nat × Nat)} {m m' : Mem} (h : KeepHi s lo m m')
    (hw : ∀ p ∈ lo, ∃ q ∈ lo', q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) : KeepHi s lo' m m' :=
  fun a n h₀ ha hl => h a n h₀ ha fun p hp => by
    obtain ⟨q, hq, h₁, h₂⟩ := hw p hp
    rcases hl q hq with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)

/-- Stores to bytes of `scratch` at `[o, o + n)`. -/
theorem keepHi_of_out {s : State} {o n : Nat} {m m' : Mem} (h : Outside (sc s) o n m m') :
    KeepHi s [(o, n)] m m' := fun a k _ ha hl => by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  rw [scA, off_add]
  refine h _ ?_
  rw [ofs_off0 _ (by unfold scrBytes at ha; omega)]
  have := hl _ (List.mem_singleton_self _)
  dsimp only at this
  omega

/-- A store to the frame keeps `scratch`. -/
theorem keepHi_of_slot {s : State} (hp : DPre s) {d : Nat} (hd : d + 8 ≤ frameBytes) {m : Mem} (v : BitVec 64) :
    KeepHi s [] m (m.writeW (off (fb s) d) v) := fun a k _ ha _ => by
  obtain ⟨h1, _⟩ := scr_len hp
  refine bytes_keep ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => ?_) (by unfold scrBytes at ha; omega)
  rw [List.mem_singleton.mp hr]
  exact ((hp.dKs.sub_left (frame_sub s hd)).sub_right (sub_trans (scSub ha) (Region.sub_prefix h1))).symm

/-- `scratch + d + 32 i`, from the five doublings of `i`. -/
theorem dst_addr (x : Addr) {i d : Nat} :
    BitVec.ofNat 64 i + BitVec.ofNat 64 i + (BitVec.ofNat 64 i + BitVec.ofNat 64 i) +
          (BitVec.ofNat 64 i + BitVec.ofNat 64 i + (BitVec.ofNat 64 i + BitVec.ofNat 64 i)) +
        (BitVec.ofNat 64 i + BitVec.ofNat 64 i + (BitVec.ofNat 64 i + BitVec.ofNat 64 i) +
          (BitVec.ofNat 64 i + BitVec.ofNat 64 i + (BitVec.ofNat 64 i + BitVec.ofNat 64 i))) +
      (BitVec.ofNat 64 i + BitVec.ofNat 64 i + (BitVec.ofNat 64 i + BitVec.ofNat 64 i) +
          (BitVec.ofNat 64 i + BitVec.ofNat 64 i + (BitVec.ofNat 64 i + BitVec.ofNat 64 i)) +
        (BitVec.ofNat 64 i + BitVec.ofNat 64 i + (BitVec.ofNat 64 i + BitVec.ofNat 64 i) +
          (BitVec.ofNat 64 i + BitVec.ofNat 64 i + (BitVec.ofNat 64 i + BitVec.ofNat 64 i)))) + x +
      BitVec.ofNat 64 d = off x (d + 32 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem prfStart_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {i : Nat} (hI : word t.mem (fb s) oI = BitVec.ofNat 64 i) :
    WP isa (.block [.mov .rdi (.mem (sp oScr)), .mov .rax (.mem (sp oI)), .mov .r9 (.mem (sp oK))]) t
      fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = sc s ∧ t'.gpr .rax = BitVec.ofNat 64 i ∧
        t'.gpr .r9 = s.gpr .r8 := by
  have hs := hc.frm hp
  refine (WP.keep [.rdi, .rax, .r9] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rdi = sc s ∧
    t'.gpr .rax = BitVec.ofNat 64 i ∧ t'.gpr .r9 = s.gpr .r8) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h⟩
  xrun [ea_sp, hc.rsp, hs.ld (d := oScr) (by decide), hs.ld (d := oI) (by decide), hs.ld (d := oK) (by decide),
    hc.slots.sScr, hc.slots.sK, hI]

theorem prfUpdArgs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {L : Nat} (hL : L < 2 ^ 31) :
    WP isa (.block (prfUpdArgs L)) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0 ∧
      t'.gpr .rsi = BitVec.ofNat 64 64 ∧ t'.gpr .rdx = scA s sMsg ∧ (t'.gpr .rcx).toNat = L ∧
      t'.gpr .r8 = scA s sWork := by
  have hs := hc.frm hp
  refine (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (c := .block (prfUpdArgs L)) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .rdi = scA s 0 ∧ t'.gpr .rsi = BitVec.ofNat 64 64 ∧ t'.gpr .rdx = scA s sMsg ∧
    (t'.gpr .rcx).toNat = L ∧ t'.gpr .r8 = scA s sWork) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h⟩
  xrun [prfUpdArgs, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide),
    hc.slots.sScr, scA_zero, sx (d := sMsg) (by decide), sx (d := sWork) (by decide)]
  simp; omega

theorem prfFinArgs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {L dst i : Nat} (hL : 64 + L < 2 ^ 31) (hd : dst < 2 ^ 31) (hI : word t.mem (fb s) oI = BitVec.ofNat 64 i) :
    WP isa (.block (prfFinArgs L dst)) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0 ∧
      t'.gpr .rsi = scA s sOuter ∧ t'.gpr .rdx = BitVec.ofNat 64 (64 + L) ∧ t'.gpr .rcx = scA s (dst + 32 * i) ∧
      t'.gpr .r8 = scA s sWork := by
  have hs := hc.frm hp
  refine (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (c := .block (prfFinArgs L dst)) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .rdi = scA s 0 ∧ t'.gpr .rsi = scA s sOuter ∧ t'.gpr .rdx = BitVec.ofNat 64 (64 + L) ∧
    t'.gpr .rcx = scA s (dst + 32 * i) ∧ t'.gpr .r8 = scA s sWork) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h⟩
  xrun [prfFinArgs, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide),
    hs.ld (d := oI) (by decide), hc.slots.sScr, hI, scA_zero, sx (d := sOuter) (by decide),
    sx (d := sWork) (by decide), sx hd, dst_addr]
  exact BitVec.eq_of_toNat_eq (by simp; omega)


/-- The number of `AM`'s blocks. -/
abbrev nbOf (s : State) : Nat := (kOf s + 31) / 32

/-- What `incr` leaves. -/
structure Incr (s : State) (R : BitVec 64) (EM : List Byte) (t : State) (i N : Nat) (t' : State) : Prop where
  ctx : Ctx s R EM t'
  zf : t'.zf = some (decide (i + 1 = N))
  sI : word t'.mem (fb s) oI = BitVec.ofNat 64 (i + 1)
  sNB : word t'.mem (fb s) oNB = word t.mem (fb s) oNB
  keep : KeepHi s [] t.mem t'.mem

theorem incr_post {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t t' : State} (hc : Ctx s R EM t)
    {i N : Nat} (hm : t'.mem = t.mem.writeW (off (fb s) oI) (BitVec.ofNat 64 (i + 1)))
    (hz : t'.zf = some (decide (i + 1 = N))) (k : Keep [.rax] t t') : Incr s R EM t i N t' := by
  have hfw : Frame [⟨off (fb s) oI, 8⟩] t.mem t'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.step hp k.2.1 k.2.2 (k.gpr (by decide)) hfw fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr (Region.sub_prefix (by decide))), hz,
    by rw [hm]; exact word_writeW_self _ _ _ _,
    by rw [hm]; exact word_ww _ _ _ (by decide) (by decide) (by decide), by rw [hm]; exact keepHi_of_slot hp (by decide) _⟩

theorem incr8_ok {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {i : Nat} (hi : i < 8) (hI : word t.mem (fb s) oI = BitVec.ofNat 64 i) :
    WP isa (.block (incr (.imm 8))) t (Incr s R EM t i 8) := by
  have hs := hc.frm hp
  refine (WP.keep [.rax] (c := .block (incr (.imm 8))) (Q := fun t' =>
    t'.mem = t.mem.writeW (off (fb s) oI) (BitVec.ofNat 64 (i + 1)) ∧ t'.zf = some (decide (i + 1 = 8))) ?_
      rfl).mono fun t' ⟨⟨hm, hz⟩, k⟩ => incr_post hp hc hm hz k
  xrun [incr, ea_sp, hc.rsp, hs.ld (d := oI) (by decide), hs.st (d := oI) (by decide), hI, ofNat_add_one,
    ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega) (show 8 < 2 ^ 64 by decide)]
  exact ofNat_sub_beq (N := 8) (by omega) (by decide)

theorem incrNB_ok {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {i : Nat} (hi : i < nbOf s) (hI : word t.mem (fb s) oI = BitVec.ofNat 64 i)
    (hNB : word t.mem (fb s) oNB = BitVec.ofNat 64 (nbOf s)) :
    WP isa (.block (incr (.mem (sp oNB)))) t (Incr s R EM t i (nbOf s)) := by
  have hs := hc.frm hp
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  have hnb : nbOf s ≤ 33 := by unfold nbOf; omega
  refine (WP.keep [.rax] (c := .block (incr (.mem (sp oNB)))) (Q := fun t' =>
    t'.mem = t.mem.writeW (off (fb s) oI) (BitVec.ofNat 64 (i + 1)) ∧ t'.zf = some (decide (i + 1 = nbOf s))) ?_
      rfl).mono fun t' ⟨⟨hm, hz⟩, k⟩ => incr_post hp hc hm hz k
  xrun [incr, ea_sp, hc.rsp, hs.ld (d := oI) (by decide), hs.st (d := oI) (by decide), hs.ld (d := oNB) (by decide),
    hI, ofNat_add_one, word_ww _ _ _ (show oNB + 8 ≤ oI ∨ oI + 8 ≤ oNB by decide) (by decide) (by decide), hNB,
    ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega) (show nbOf s < 2 ^ 64 by omega)]
  done


theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (off p a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, off, BitVec.add_assoc, BitVec.ofNat_add]

variable {v : Compress}

/-- After `i` blocks of IRPRF, to `scratch + dst`, from the state `t₀`
before the loop. -/
structure PInv (v : Compress) (s : State) (R : BitVec 64) (EM K : List Byte) (msg : Nat → List Byte)
    (dst N : Nat) (t₀ : State) (i : Nat) (t : State) : Prop where
  ctx : Ctx s R EM t
  sI : word t.mem (fb s) oI = BitVec.ofNat 64 i
  sNB : word t.mem (fb s) oNB = BitVec.ofNat 64 (nbOf s)
  key : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = K
  blk : Spec.Rsa.bytesAt t.mem (scA s dst) (32 * i) =
    (List.range i).flatMap fun j => Spec.Hmac.hmac Spec.Hmac.sha256 K (msg j)
  keep : KeepHi s [(sMsg, 16), (dst, 32 * N)] t₀.mem t.mem

theorem prf_body {s : State} (hp : DPre s) {R : BitVec 64} {EM K : List Byte} {msg : Nat → List Byte}
    {label : List Nat} {lenC : List Instr} {L dst N : Nat} {count : Src} {t₀ : State}
    (hL : label.length + 4 = L) (hL16 : L ≤ 16) (hd1 : sKDK + 32 ≤ dst) (hd2 : dst + 32 * N ≤ scrBytes)
    (hN : N ≤ 32) (hK : K.length = 32) (hml : ∀ i, (msg i).length = L)
    (hmsg : ∀ t i, Ctx s R EM t → i < N → t.gpr .rdi = sc s → t.gpr .rax = BitVec.ofNat 64 i →
      t.gpr .r9 = s.gpr .r8 → WP isa (.block (msgBytes label lenC)) t fun t' =>
        Outside (sc s) sMsg 16 t.mem t'.mem ∧ Spec.Rsa.bytesAt t'.mem (scA s sMsg) L = msg i ∧ Keep [.rdx] t t')
    (hincr : ∀ t i, Ctx s R EM t → i < N → word t.mem (fb s) oI = BitVec.ofNat 64 i →
      word t.mem (fb s) oNB = BitVec.ofNat 64 (nbOf s) → WP isa (.block (incr count)) t (Incr s R EM t i N))
    {i : Nat} (hi : i < N) {t : State} (h : PInv v s R EM K msg dst N t₀ i t) :
    WP isa (prfBody (HH v) label lenC dst count) t fun t' =>
      t'.zf = some (decide (i + 1 = N)) ∧ PInv v s R EM K msg dst N t₀ (i + 1) t' := by
  have hhd : sMsg + 16 ≤ dst := by unfold sMsg sKDK at *; omega
  subst hL
  refine WP.seq (WP.mono (prfStart_run hp h.ctx h.sI) fun t₁ ⟨hc₁, hm₁, hdi₁, hax₁, h9₁⟩ => ?_)
  refine WP.seq (WP.mono (hmsg t₁ i hc₁ hi hdi₁ hax₁ h9₁) fun t₂ ⟨ho₂, hb₂, k₂⟩ => ?_)
  have hf₂ : Frame [⟨scA s sMsg, 16⟩] t₁.mem t₂.mem := frame_of_out ho₂ (by decide)
  have hc₂ : Ctx s R EM t₂ := hc₁.step hp k₂.2.1 k₂.2.2 (k₂.gpr (by decide)) hf₂ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact scS (by decide)
  have fk₂ : FrmKeep s t.mem t₂.mem := (FrmKeep.eq hm₁).trans (frmKeep_of_frame (lo := [(sMsg, 16)]) (ws := [⟨scA s sMsg, 16⟩])
    (n := 0) hp (by decide) (hf₂.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
    fun r hr => ⟨sMsg, 16, List.mem_singleton.mp hr, by decide, .inr (List.mem_singleton_self _)⟩)
  have kh₂ : KeepHi s [(sMsg, 16)] t.mem t₂.mem := by rw [KeepHi, ← hm₁]; exact keepHi_of_out ho₂
  have hk₂ : Spec.Rsa.bytesAt t₂.mem (scA s sKDK) 32 = K := by
    rw [kh₂ _ _ (by decide) (by decide) (by simp; decide)]; exact h.key
  obtain ⟨h1, -⟩ := scr_len hp
  have hX : Spec.Rsa.bytesAt t₂.mem (scA s sMsg) (label.length + 4) = msg i := hb₂
  refine mac_front hp hc₂ (kOff := sKDK) (by decide) (by decide) (fun _ hc => prfUpdArgs_run hp hc (by omega))
    (Covers.of_sub fun r hr => ⟨scrR s, List.mem_append_right _ (by rw [hp.hwr]; simp [scrR]), sMsg,
      by rw [List.mem_singleton.mp hr]; rfl, by rw [List.mem_singleton.mp hr]; dsimp only [scrR]; unfold scrBytes sMsg at *; omega⟩)
    (fun a n han => scD (.inr han) (by unfold scrBytes sMsg; omega) (by unfold scrBytes sMsg at *; omega))
    (stkD hp (by decide) (by unfold scrBytes sMsg; omega)) (by omega) fun t₃ h₃ => ?_
  rw [hk₂, hX] at h₃
  have hI₃ : word t₃.mem (fb s) oI = BitVec.ofNat 64 i := by
    rw [h₃.frm _ (by decide), fk₂ _ (by decide)]; exact h.sI
  refine WP.seq (WP.mono (prfFinArgs_run hp h₃.ctx (L := label.length + 4) (dst := dst) (by omega)
    (by unfold scrBytes at hd2; omega) hI₃) fun t₄ ⟨hc₄, hm₄, hdi₄, hsi₄, hdx₄, hcx₄, h8₄⟩ => ?_)
  have h₄ : MacMid v s R EM K (msg i) t₂ t₄ := ⟨hc₄, by rw [hm₄]; exact h₃.inner, by rw [hm₄]; exact h₃.outer,
    by rw [KeepHi, hm₄]; exact h₃.keep, by rw [FrmKeep, hm₄]; exact h₃.frm⟩
  refine WP.seq (WP.mono (mac_fin hp h₄ (dOff := dst + 32 * i) (by unfold sMsg sKDK at *; omega)
    (by omega) hK hdi₄ hsi₄ (by rw [hdx₄, hml]) hcx₄ h8₄ (by rw [hml]; omega))
    fun t₅ ⟨hc₅, hb₅, kh₅, fk₅⟩ => ?_)
  have fk₂₅ := fk₂.trans fk₅
  refine WP.mono (hincr t₅ i hc₅ hi (by rw [fk₂₅ _ (by decide)]; exact h.sI)
    (by rw [fk₂₅ _ (by decide)]; exact h.sNB)) fun t₆ h₆ => ⟨h₆.zf, ?_⟩
  have kh : KeepHi s ([(sMsg, 16)] ++ [(dst + 32 * i, 32)] ++ []) t.mem t₆.mem := (kh₂.trans kh₅).trans h₆.keep
  refine ⟨h₆.ctx, h₆.sI, by rw [h₆.sNB, fk₂₅ _ (by decide)]; exact h.sNB, ?_, ?_, ?_⟩
  · rw [kh _ _ (by decide) (by decide) (by simp; unfold sMsg sKDK at *; omega)]; exact h.key
  · rw [show 32 * (i + 1) = 32 * i + 32 by ring_nf, bytesAt_add, kh _ _ (by unfold sMsg sKDK at *; omega)
      (by omega) (by simp; omega), h.blk, scA, off_off, ← scA, h₆.keep _ _ (by unfold sMsg sKDK at *; omega)
      (by omega) (by simp), hb₅, List.range_succ, List.flatMap_append, List.flatMap_singleton]
  · exact (h.keep.trans kh).widen fun p hp => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., le_refl _, le_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), le_refl _, le_refl _⟩
      · exact ⟨_, List.mem_cons_self .., le_refl _, le_refl _⟩
      · exact ⟨(dst, 32 * N), List.mem_cons_of_mem _ (List.mem_singleton_self _), by simp, by simp; omega⟩


theorem msgCL_len (i : Nat) : (msgCL i).length = 10 := by
  simp [msgCL, Spec.Rsa.i2osp, Spec.RsaPkcs1Enc.ascii]

theorem msgAM_len (k i : Nat) : (msgAM k i).length = 11 := by
  simp [msgAM, Spec.Rsa.i2osp, Spec.RsaPkcs1Enc.ascii]

/-- The loop of IRPRF's blocks. -/
theorem prf_loop {s : State} (hp : DPre s) {R : BitVec 64} {EM K : List Byte} {msg : Nat → List Byte}
    {label : List Nat} {lenC : List Instr} {L dst N : Nat} {count : Src} {t₀ : State}
    (hL : label.length + 4 = L) (hL16 : L ≤ 16) (hd1 : sKDK + 32 ≤ dst) (hd2 : dst + 32 * N ≤ scrBytes)
    (hN0 : 0 < N) (hN : N ≤ 32) (hK : K.length = 32) (hml : ∀ i, (msg i).length = L)
    (hmsg : ∀ t i, Ctx s R EM t → i < N → t.gpr .rdi = sc s → t.gpr .rax = BitVec.ofNat 64 i →
      t.gpr .r9 = s.gpr .r8 → WP isa (.block (msgBytes label lenC)) t fun t' =>
        Outside (sc s) sMsg 16 t.mem t'.mem ∧ Spec.Rsa.bytesAt t'.mem (scA s sMsg) L = msg i ∧ Keep [.rdx] t t')
    (hincr : ∀ t i, Ctx s R EM t → i < N → word t.mem (fb s) oI = BitVec.ofNat 64 i →
      word t.mem (fb s) oNB = BitVec.ofNat 64 (nbOf s) → WP isa (.block (incr count)) t (Incr s R EM t i N))
    (h0 : PInv v s R EM K msg dst N t₀ 0 t₀) :
    WP isa (.loop (prfBody (HH v) label lenC dst count) .ne) t₀ (PInv v s R EM K msg dst N t₀ N) :=
  wp_upto (a := 0) (N := N) hN0 (PInv v s R EM K msg dst N t₀)
    (fun _ _ hj _ hI => prf_body hp hL hL16 hd1 hd2 hN hK hml hmsg hincr hj hI) (fun _ h => h) h0

/-- The start of a loop. -/
theorem pinv0 {s : State} {R : BitVec 64} {EM K : List Byte} {msg : Nat → List Byte} {dst N : Nat} {t : State}
    (hc : Ctx s R EM t) (hI : word t.mem (fb s) oI = BitVec.ofNat 64 0)
    (hNB : word t.mem (fb s) oNB = BitVec.ofNat 64 (nbOf s)) (hk : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = K) :
    PInv v s R EM K msg dst N t 0 t :=
  ⟨hc, hI, hNB, hk, by simp [Spec.Rsa.bytesAt], KeepHi.refl _ _ _⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
