// The functions of `src/internal/vg_brainpoolp320r1_windows.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_windows:
	std %r31, 1864(%r3)
	mflr %r0
	std %r0, 1872(%r3)
	ld %r4, 184(%r3)
	std %r4, 5056(%r3)
	ld %r4, 192(%r3)
	std %r4, 5064(%r3)
	ld %r4, 200(%r3)
	std %r4, 5072(%r3)
	ld %r4, 208(%r3)
	std %r4, 5080(%r3)
	ld %r4, 216(%r3)
	std %r4, 5088(%r3)
	ld %r4, 264(%r3)
	std %r4, 5096(%r3)
	ld %r4, 272(%r3)
	std %r4, 5104(%r3)
	ld %r4, 280(%r3)
	std %r4, 5112(%r3)
	ld %r4, 288(%r3)
	std %r4, 5120(%r3)
	ld %r4, 296(%r3)
	std %r4, 5128(%r3)
	ld %r4, 184(%r3)
	std %r4, 5136(%r3)
	ld %r4, 192(%r3)
	std %r4, 5144(%r3)
	ld %r4, 200(%r3)
	std %r4, 5152(%r3)
	ld %r4, 208(%r3)
	std %r4, 5160(%r3)
	ld %r4, 216(%r3)
	std %r4, 5168(%r3)
	ld %r4, 1584(%r3)
	std %r4, 5176(%r3)
	ld %r4, 1592(%r3)
	std %r4, 5184(%r3)
	ld %r4, 1600(%r3)
	std %r4, 5192(%r3)
	ld %r4, 1608(%r3)
	std %r4, 5200(%r3)
	ld %r4, 1616(%r3)
	std %r4, 5208(%r3)
	ld %r4, 1784(%r3)
	std %r4, 5216(%r3)
	ld %r4, 1792(%r3)
	std %r4, 5224(%r3)
	ld %r4, 1800(%r3)
	std %r4, 5232(%r3)
	ld %r4, 1808(%r3)
	std %r4, 5240(%r3)
	ld %r4, 1816(%r3)
	std %r4, 5248(%r3)
	ld %r4, 264(%r3)
	std %r4, 5256(%r3)
	ld %r4, 272(%r3)
	std %r4, 5264(%r3)
	ld %r4, 280(%r3)
	std %r4, 5272(%r3)
	ld %r4, 288(%r3)
	std %r4, 5280(%r3)
	ld %r4, 296(%r3)
	std %r4, 5288(%r3)
	ld %r4, 1584(%r3)
	std %r4, 744(%r3)
	ld %r4, 1592(%r3)
	std %r4, 752(%r3)
	ld %r4, 1600(%r3)
	std %r4, 760(%r3)
	ld %r4, 1608(%r3)
	std %r4, 768(%r3)
	ld %r4, 1616(%r3)
	std %r4, 776(%r3)
	ld %r4, 1784(%r3)
	std %r4, 784(%r3)
	ld %r4, 1792(%r3)
	std %r4, 792(%r3)
	ld %r4, 1800(%r3)
	std %r4, 800(%r3)
	ld %r4, 1808(%r3)
	std %r4, 808(%r3)
	ld %r4, 1816(%r3)
	std %r4, 816(%r3)
	ld %r4, 264(%r3)
	std %r4, 824(%r3)
	ld %r4, 272(%r3)
	std %r4, 832(%r3)
	ld %r4, 280(%r3)
	std %r4, 840(%r3)
	ld %r4, 288(%r3)
	std %r4, 848(%r3)
	ld %r4, 296(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5296(%r3)
	ld %r4, 872(%r3)
	std %r4, 5304(%r3)
	ld %r4, 880(%r3)
	std %r4, 5312(%r3)
	ld %r4, 888(%r3)
	std %r4, 5320(%r3)
	ld %r4, 896(%r3)
	std %r4, 5328(%r3)
	ld %r4, 904(%r3)
	std %r4, 5336(%r3)
	ld %r4, 912(%r3)
	std %r4, 5344(%r3)
	ld %r4, 920(%r3)
	std %r4, 5352(%r3)
	ld %r4, 928(%r3)
	std %r4, 5360(%r3)
	ld %r4, 936(%r3)
	std %r4, 5368(%r3)
	ld %r4, 944(%r3)
	std %r4, 5376(%r3)
	ld %r4, 952(%r3)
	std %r4, 5384(%r3)
	ld %r4, 960(%r3)
	std %r4, 5392(%r3)
	ld %r4, 968(%r3)
	std %r4, 5400(%r3)
	ld %r4, 976(%r3)
	std %r4, 5408(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5416(%r3)
	ld %r4, 872(%r3)
	std %r4, 5424(%r3)
	ld %r4, 880(%r3)
	std %r4, 5432(%r3)
	ld %r4, 888(%r3)
	std %r4, 5440(%r3)
	ld %r4, 896(%r3)
	std %r4, 5448(%r3)
	ld %r4, 904(%r3)
	std %r4, 5456(%r3)
	ld %r4, 912(%r3)
	std %r4, 5464(%r3)
	ld %r4, 920(%r3)
	std %r4, 5472(%r3)
	ld %r4, 928(%r3)
	std %r4, 5480(%r3)
	ld %r4, 936(%r3)
	std %r4, 5488(%r3)
	ld %r4, 944(%r3)
	std %r4, 5496(%r3)
	ld %r4, 952(%r3)
	std %r4, 5504(%r3)
	ld %r4, 960(%r3)
	std %r4, 5512(%r3)
	ld %r4, 968(%r3)
	std %r4, 5520(%r3)
	ld %r4, 976(%r3)
	std %r4, 5528(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5536(%r3)
	ld %r4, 872(%r3)
	std %r4, 5544(%r3)
	ld %r4, 880(%r3)
	std %r4, 5552(%r3)
	ld %r4, 888(%r3)
	std %r4, 5560(%r3)
	ld %r4, 896(%r3)
	std %r4, 5568(%r3)
	ld %r4, 904(%r3)
	std %r4, 5576(%r3)
	ld %r4, 912(%r3)
	std %r4, 5584(%r3)
	ld %r4, 920(%r3)
	std %r4, 5592(%r3)
	ld %r4, 928(%r3)
	std %r4, 5600(%r3)
	ld %r4, 936(%r3)
	std %r4, 5608(%r3)
	ld %r4, 944(%r3)
	std %r4, 5616(%r3)
	ld %r4, 952(%r3)
	std %r4, 5624(%r3)
	ld %r4, 960(%r3)
	std %r4, 5632(%r3)
	ld %r4, 968(%r3)
	std %r4, 5640(%r3)
	ld %r4, 976(%r3)
	std %r4, 5648(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5656(%r3)
	ld %r4, 872(%r3)
	std %r4, 5664(%r3)
	ld %r4, 880(%r3)
	std %r4, 5672(%r3)
	ld %r4, 888(%r3)
	std %r4, 5680(%r3)
	ld %r4, 896(%r3)
	std %r4, 5688(%r3)
	ld %r4, 904(%r3)
	std %r4, 5696(%r3)
	ld %r4, 912(%r3)
	std %r4, 5704(%r3)
	ld %r4, 920(%r3)
	std %r4, 5712(%r3)
	ld %r4, 928(%r3)
	std %r4, 5720(%r3)
	ld %r4, 936(%r3)
	std %r4, 5728(%r3)
	ld %r4, 944(%r3)
	std %r4, 5736(%r3)
	ld %r4, 952(%r3)
	std %r4, 5744(%r3)
	ld %r4, 960(%r3)
	std %r4, 5752(%r3)
	ld %r4, 968(%r3)
	std %r4, 5760(%r3)
	ld %r4, 976(%r3)
	std %r4, 5768(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5776(%r3)
	ld %r4, 872(%r3)
	std %r4, 5784(%r3)
	ld %r4, 880(%r3)
	std %r4, 5792(%r3)
	ld %r4, 888(%r3)
	std %r4, 5800(%r3)
	ld %r4, 896(%r3)
	std %r4, 5808(%r3)
	ld %r4, 904(%r3)
	std %r4, 5816(%r3)
	ld %r4, 912(%r3)
	std %r4, 5824(%r3)
	ld %r4, 920(%r3)
	std %r4, 5832(%r3)
	ld %r4, 928(%r3)
	std %r4, 5840(%r3)
	ld %r4, 936(%r3)
	std %r4, 5848(%r3)
	ld %r4, 944(%r3)
	std %r4, 5856(%r3)
	ld %r4, 952(%r3)
	std %r4, 5864(%r3)
	ld %r4, 960(%r3)
	std %r4, 5872(%r3)
	ld %r4, 968(%r3)
	std %r4, 5880(%r3)
	ld %r4, 976(%r3)
	std %r4, 5888(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5896(%r3)
	ld %r4, 872(%r3)
	std %r4, 5904(%r3)
	ld %r4, 880(%r3)
	std %r4, 5912(%r3)
	ld %r4, 888(%r3)
	std %r4, 5920(%r3)
	ld %r4, 896(%r3)
	std %r4, 5928(%r3)
	ld %r4, 904(%r3)
	std %r4, 5936(%r3)
	ld %r4, 912(%r3)
	std %r4, 5944(%r3)
	ld %r4, 920(%r3)
	std %r4, 5952(%r3)
	ld %r4, 928(%r3)
	std %r4, 5960(%r3)
	ld %r4, 936(%r3)
	std %r4, 5968(%r3)
	ld %r4, 944(%r3)
	std %r4, 5976(%r3)
	ld %r4, 952(%r3)
	std %r4, 5984(%r3)
	ld %r4, 960(%r3)
	std %r4, 5992(%r3)
	ld %r4, 968(%r3)
	std %r4, 6000(%r3)
	ld %r4, 976(%r3)
	std %r4, 6008(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6016(%r3)
	ld %r4, 872(%r3)
	std %r4, 6024(%r3)
	ld %r4, 880(%r3)
	std %r4, 6032(%r3)
	ld %r4, 888(%r3)
	std %r4, 6040(%r3)
	ld %r4, 896(%r3)
	std %r4, 6048(%r3)
	ld %r4, 904(%r3)
	std %r4, 6056(%r3)
	ld %r4, 912(%r3)
	std %r4, 6064(%r3)
	ld %r4, 920(%r3)
	std %r4, 6072(%r3)
	ld %r4, 928(%r3)
	std %r4, 6080(%r3)
	ld %r4, 936(%r3)
	std %r4, 6088(%r3)
	ld %r4, 944(%r3)
	std %r4, 6096(%r3)
	ld %r4, 952(%r3)
	std %r4, 6104(%r3)
	ld %r4, 960(%r3)
	std %r4, 6112(%r3)
	ld %r4, 968(%r3)
	std %r4, 6120(%r3)
	ld %r4, 976(%r3)
	std %r4, 6128(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6136(%r3)
	ld %r4, 872(%r3)
	std %r4, 6144(%r3)
	ld %r4, 880(%r3)
	std %r4, 6152(%r3)
	ld %r4, 888(%r3)
	std %r4, 6160(%r3)
	ld %r4, 896(%r3)
	std %r4, 6168(%r3)
	ld %r4, 904(%r3)
	std %r4, 6176(%r3)
	ld %r4, 912(%r3)
	std %r4, 6184(%r3)
	ld %r4, 920(%r3)
	std %r4, 6192(%r3)
	ld %r4, 928(%r3)
	std %r4, 6200(%r3)
	ld %r4, 936(%r3)
	std %r4, 6208(%r3)
	ld %r4, 944(%r3)
	std %r4, 6216(%r3)
	ld %r4, 952(%r3)
	std %r4, 6224(%r3)
	ld %r4, 960(%r3)
	std %r4, 6232(%r3)
	ld %r4, 968(%r3)
	std %r4, 6240(%r3)
	ld %r4, 976(%r3)
	std %r4, 6248(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6256(%r3)
	ld %r4, 872(%r3)
	std %r4, 6264(%r3)
	ld %r4, 880(%r3)
	std %r4, 6272(%r3)
	ld %r4, 888(%r3)
	std %r4, 6280(%r3)
	ld %r4, 896(%r3)
	std %r4, 6288(%r3)
	ld %r4, 904(%r3)
	std %r4, 6296(%r3)
	ld %r4, 912(%r3)
	std %r4, 6304(%r3)
	ld %r4, 920(%r3)
	std %r4, 6312(%r3)
	ld %r4, 928(%r3)
	std %r4, 6320(%r3)
	ld %r4, 936(%r3)
	std %r4, 6328(%r3)
	ld %r4, 944(%r3)
	std %r4, 6336(%r3)
	ld %r4, 952(%r3)
	std %r4, 6344(%r3)
	ld %r4, 960(%r3)
	std %r4, 6352(%r3)
	ld %r4, 968(%r3)
	std %r4, 6360(%r3)
	ld %r4, 976(%r3)
	std %r4, 6368(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6376(%r3)
	ld %r4, 872(%r3)
	std %r4, 6384(%r3)
	ld %r4, 880(%r3)
	std %r4, 6392(%r3)
	ld %r4, 888(%r3)
	std %r4, 6400(%r3)
	ld %r4, 896(%r3)
	std %r4, 6408(%r3)
	ld %r4, 904(%r3)
	std %r4, 6416(%r3)
	ld %r4, 912(%r3)
	std %r4, 6424(%r3)
	ld %r4, 920(%r3)
	std %r4, 6432(%r3)
	ld %r4, 928(%r3)
	std %r4, 6440(%r3)
	ld %r4, 936(%r3)
	std %r4, 6448(%r3)
	ld %r4, 944(%r3)
	std %r4, 6456(%r3)
	ld %r4, 952(%r3)
	std %r4, 6464(%r3)
	ld %r4, 960(%r3)
	std %r4, 6472(%r3)
	ld %r4, 968(%r3)
	std %r4, 6480(%r3)
	ld %r4, 976(%r3)
	std %r4, 6488(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6496(%r3)
	ld %r4, 872(%r3)
	std %r4, 6504(%r3)
	ld %r4, 880(%r3)
	std %r4, 6512(%r3)
	ld %r4, 888(%r3)
	std %r4, 6520(%r3)
	ld %r4, 896(%r3)
	std %r4, 6528(%r3)
	ld %r4, 904(%r3)
	std %r4, 6536(%r3)
	ld %r4, 912(%r3)
	std %r4, 6544(%r3)
	ld %r4, 920(%r3)
	std %r4, 6552(%r3)
	ld %r4, 928(%r3)
	std %r4, 6560(%r3)
	ld %r4, 936(%r3)
	std %r4, 6568(%r3)
	ld %r4, 944(%r3)
	std %r4, 6576(%r3)
	ld %r4, 952(%r3)
	std %r4, 6584(%r3)
	ld %r4, 960(%r3)
	std %r4, 6592(%r3)
	ld %r4, 968(%r3)
	std %r4, 6600(%r3)
	ld %r4, 976(%r3)
	std %r4, 6608(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6616(%r3)
	ld %r4, 872(%r3)
	std %r4, 6624(%r3)
	ld %r4, 880(%r3)
	std %r4, 6632(%r3)
	ld %r4, 888(%r3)
	std %r4, 6640(%r3)
	ld %r4, 896(%r3)
	std %r4, 6648(%r3)
	ld %r4, 904(%r3)
	std %r4, 6656(%r3)
	ld %r4, 912(%r3)
	std %r4, 6664(%r3)
	ld %r4, 920(%r3)
	std %r4, 6672(%r3)
	ld %r4, 928(%r3)
	std %r4, 6680(%r3)
	ld %r4, 936(%r3)
	std %r4, 6688(%r3)
	ld %r4, 944(%r3)
	std %r4, 6696(%r3)
	ld %r4, 952(%r3)
	std %r4, 6704(%r3)
	ld %r4, 960(%r3)
	std %r4, 6712(%r3)
	ld %r4, 968(%r3)
	std %r4, 6720(%r3)
	ld %r4, 976(%r3)
	std %r4, 6728(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6736(%r3)
	ld %r4, 872(%r3)
	std %r4, 6744(%r3)
	ld %r4, 880(%r3)
	std %r4, 6752(%r3)
	ld %r4, 888(%r3)
	std %r4, 6760(%r3)
	ld %r4, 896(%r3)
	std %r4, 6768(%r3)
	ld %r4, 904(%r3)
	std %r4, 6776(%r3)
	ld %r4, 912(%r3)
	std %r4, 6784(%r3)
	ld %r4, 920(%r3)
	std %r4, 6792(%r3)
	ld %r4, 928(%r3)
	std %r4, 6800(%r3)
	ld %r4, 936(%r3)
	std %r4, 6808(%r3)
	ld %r4, 944(%r3)
	std %r4, 6816(%r3)
	ld %r4, 952(%r3)
	std %r4, 6824(%r3)
	ld %r4, 960(%r3)
	std %r4, 6832(%r3)
	ld %r4, 968(%r3)
	std %r4, 6840(%r3)
	ld %r4, 976(%r3)
	std %r4, 6848(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6856(%r3)
	ld %r4, 872(%r3)
	std %r4, 6864(%r3)
	ld %r4, 880(%r3)
	std %r4, 6872(%r3)
	ld %r4, 888(%r3)
	std %r4, 6880(%r3)
	ld %r4, 896(%r3)
	std %r4, 6888(%r3)
	ld %r4, 904(%r3)
	std %r4, 6896(%r3)
	ld %r4, 912(%r3)
	std %r4, 6904(%r3)
	ld %r4, 920(%r3)
	std %r4, 6912(%r3)
	ld %r4, 928(%r3)
	std %r4, 6920(%r3)
	ld %r4, 936(%r3)
	std %r4, 6928(%r3)
	ld %r4, 944(%r3)
	std %r4, 6936(%r3)
	ld %r4, 952(%r3)
	std %r4, 6944(%r3)
	ld %r4, 960(%r3)
	std %r4, 6952(%r3)
	ld %r4, 968(%r3)
	std %r4, 6960(%r3)
	ld %r4, 976(%r3)
	std %r4, 6968(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	ld %r4, 184(%r3)
	std %r4, 624(%r3)
	ld %r4, 192(%r3)
	std %r4, 632(%r3)
	ld %r4, 200(%r3)
	std %r4, 640(%r3)
	ld %r4, 208(%r3)
	std %r4, 648(%r3)
	ld %r4, 216(%r3)
	std %r4, 656(%r3)
	ld %r4, 264(%r3)
	std %r4, 664(%r3)
	ld %r4, 272(%r3)
	std %r4, 672(%r3)
	ld %r4, 280(%r3)
	std %r4, 680(%r3)
	ld %r4, 288(%r3)
	std %r4, 688(%r3)
	ld %r4, 296(%r3)
	std %r4, 696(%r3)
	ld %r4, 184(%r3)
	std %r4, 704(%r3)
	ld %r4, 192(%r3)
	std %r4, 712(%r3)
	ld %r4, 200(%r3)
	std %r4, 720(%r3)
	ld %r4, 208(%r3)
	std %r4, 728(%r3)
	ld %r4, 216(%r3)
	std %r4, 736(%r3)
	li %r31, 80
20:
	addi %r31, %r31, -1
	li %r4, 744
	li %r5, 624
	li %r6, 704
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 984
	li %r5, 704
	li %r6, 704
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 784
	li %r5, 664
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 824
	li %r5, 704
	li %r6, 184
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 744
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1024
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 824
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 944
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 904
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 904
	li %r5, 1144
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 864
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 904
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1024
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 864
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 944
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 824
	li %r5, 904
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 824
	li %r5, 824
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 744
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 744
	li %r5, 744
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 744
	li %r5, 744
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 784
	li %r5, 1104
	li %r6, 744
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 784
	li %r5, 1144
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 784
	li %r5, 784
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 744
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1024
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 824
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 944
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 904
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 904
	li %r5, 1144
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 864
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 904
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1024
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 864
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 944
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 824
	li %r5, 904
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 824
	li %r5, 824
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 744
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 744
	li %r5, 744
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 744
	li %r5, 744
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 784
	li %r5, 1104
	li %r6, 744
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 784
	li %r5, 1144
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 784
	li %r5, 784
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 624
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 984
	li %r5, 824
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 704
	li %r5, 984
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 664
	li %r5, 784
	li %r6, 184
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r5, 704(%r3)
	ld %r4, 712(%r3)
	or %r5, %r5, %r4
	ld %r4, 720(%r3)
	or %r5, %r5, %r4
	ld %r4, 728(%r3)
	or %r5, %r5, %r4
	ld %r4, 736(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	or %r10, %r5, %r5
	ld %r4, 264(%r3)
	ld %r5, 664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 272(%r3)
	ld %r5, 672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 280(%r3)
	ld %r5, 680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 288(%r3)
	ld %r5, 688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 296(%r3)
	ld %r5, 696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	rldicr %r4, %r31, 2, 61
	add %r4, %r3, %r4
	lbz %r9, 4099(%r4)
	add %r9, %r9, %r9
	lbz %r5, 4098(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4097(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4096(%r4)
	add %r9, %r9, %r5
	li %r5, 0
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5056(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5064(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5072(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5080(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5088(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5096(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5104(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5112(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5120(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5128(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5136(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5144(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 1
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 2
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5400(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5408(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 3
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5416(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 4
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5584(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5592(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5600(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5608(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5616(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5624(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5632(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5640(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 5
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5656(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5736(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5744(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5752(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5760(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5768(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 6
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5776(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5800(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5808(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5816(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5824(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5832(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 7
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5976(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5984(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5992(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6000(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6008(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 8
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6016(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6056(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6064(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6072(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6080(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6088(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6096(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6104(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6112(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6120(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6128(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 9
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6136(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6144(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 10
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 11
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6400(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6408(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6416(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 12
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6584(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6592(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6600(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6608(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 13
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6616(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6624(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6632(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6640(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6656(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 14
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6736(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6744(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6752(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6760(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6768(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6776(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6800(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6808(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6816(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6824(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6832(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 15
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 624
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 664
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 704
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 624
	li %r6, 664
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 624
	li %r6, 704
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 664
	li %r6, 704
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 624(%r3)
	ld %r4, 872(%r3)
	std %r4, 632(%r3)
	ld %r4, 880(%r3)
	std %r4, 640(%r3)
	ld %r4, 888(%r3)
	std %r4, 648(%r3)
	ld %r4, 896(%r3)
	std %r4, 656(%r3)
	ld %r4, 904(%r3)
	std %r4, 664(%r3)
	ld %r4, 912(%r3)
	std %r4, 672(%r3)
	ld %r4, 920(%r3)
	std %r4, 680(%r3)
	ld %r4, 928(%r3)
	std %r4, 688(%r3)
	ld %r4, 936(%r3)
	std %r4, 696(%r3)
	ld %r4, 944(%r3)
	std %r4, 704(%r3)
	ld %r4, 952(%r3)
	std %r4, 712(%r3)
	ld %r4, 960(%r3)
	std %r4, 720(%r3)
	ld %r4, 968(%r3)
	std %r4, 728(%r3)
	ld %r4, 976(%r3)
	std %r4, 736(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	ld %r0, 1872(%r3)
	mtlr %r0
	ld %r31, 1864(%r3)
	blr
