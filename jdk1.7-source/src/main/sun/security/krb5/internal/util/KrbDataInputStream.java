/*
 * Copyright (c) 2000, 2005, Oracle and/or its affiliates. All rights reserved.
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

/*
 *
 *  (C) Copyright IBM Corp. 1999 All Rights Reserved.
 *  Copyright 1997 The Open Group Research Institute.  All rights reserved.
 */

package sun.security.krb5.internal.util;

import java.io.BufferedInputStream;
import java.io.InputStream;
import java.io.IOException;

/**
 * This class implements a buffered input stream. It provides methods to read a chunck
 * of data from underlying data stream.
 *
 * @author Yanni Zhang
 *
 */
public class KrbDataInputStream extends BufferedInputStream{
    private boolean bigEndian = true;

    public void setNativeByteOrder() {
        if (java.nio.ByteOrder.nativeOrder().
                equals(java.nio.ByteOrder.BIG_ENDIAN)) {
            bigEndian = true;
        } else {
            bigEndian = false;
        }
    }
    public KrbDataInputStream(InputStream is){
        super(is);
    }
    /**
     * Reads up to the specific number of bytes from this input stream.
     * @param num the number of bytes to be read.
     * @return the int value of this byte array.
     * @exception IOException.
     */
    public int read(int num) throws IOException{
        byte[] bytes = new byte[num];
        read(bytes, 0, num);
        int result = 0;
        for (int i = 0; i < num; i++) {
            if (bigEndian) {
                result |= (bytes[i] & 0xff) << (num - i - 1) * 8;
            } else {
                result |= (bytes[i] & 0xff) << i * 8;
            }
        }
        return result;
    }

    public int readVersion() throws IOException {
        // always read in big-endian mode
        int result = (read() & 0xff) << 8;
        return result | (read() & 0xff);
    }
}
