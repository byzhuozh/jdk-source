/*
 * Copyright (c) 2009, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package sun.nio.cs;

/*
 * FastPath char[]->byte[] encoder, REPLACE on malformed input or
 * unmappable input.
 */

public interface ArrayEncoder {
    int encode(char[] src, int off, int len, byte[] dst);
}
