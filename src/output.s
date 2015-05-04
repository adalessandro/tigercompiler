	.global _tigermain
_tigermain:
	movs    r4, #8
	subs    sp, sp, r4
	movs    r4, #4
	adds    r4, sp, r4
	str     lr, [r4]
	str     fp, [sp]
	movs    r4, #4
	adds    fp, sp, r4
	movs    r0, #1
	movs    r1, #1
	movs    r4, #1
	movs    r10, #1
	movs    --, #1
	str     r3, [fp, #-12]
	movs    r3, #1
	ldr     r3, [fp, #-12]
	movs    --, #1
	str     r6, [fp, #-8]
	movs    r6, #1
	ldr     r6, [fp, #-8]
	movs    --, #1
	str     r8, [fp, #-4]
	movs    r8, #1
	ldr     r8, [fp, #-4]
	movs    r2, #1
	movs    r3, #1
	adds    r0, r0, r1
	adds    r0, r0, r4
	adds    r0, r0, r10
	adds    r0, r0, --
	str     r5, [fp, #-12]
	adds    r0, r0, r5
	ldr     r5, [fp, #-12]
	adds    r0, r0, --
	str     r7, [fp, #-8]
	adds    r0, r0, r7
	ldr     r7, [fp, #-8]
	adds    r0, r0, --
	str     r9, [fp, #-4]
	adds    r0, r0, r9
	ldr     r9, [fp, #-4]
	adds    r0, r0, r2
	adds    r0, r0, r3
	movs    r0, #4
	subs    sp, fp, r0
	ldr     fp, [sp]
	movs    r9, #4
	adds    r9, sp, r9
	ldr     lr, [r9]
	movs    r9, #8
	adds    sp, sp, r9
	bx      lr
L0:
