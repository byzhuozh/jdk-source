/*
 * Copyright (c) 2000, 2007, Oracle and/or its affiliates. All rights reserved.
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

package sun.security.krb5.internal;

import sun.security.krb5.Confounder;

public class LocalSeqNumber implements SeqNumber {
    private int lastSeqNumber;

    public LocalSeqNumber() {
        randInit();
    }

    public LocalSeqNumber(int start) {
        init(start);
    }

    public LocalSeqNumber(Integer start) {
        init(start.intValue());
    }

    public synchronized void randInit() {
        /*
         * Sequence numbers fall in the range 0 through 2^32 - 1 and wrap
         * to zero following the value 2^32 - 1.
         * Previous implementations used signed sequence numbers.
         * Workaround implementation incompatibilities by not generating
         * initial sequence numbers greater than 2^30, as done
         * in MIT distribution.
         */
        // get the random confounder
        byte[] data = Confounder.bytes(4);
        data[0] = (byte)(data[0] & 0x3f);
        int result = ((data[3] & 0xff) |
                        ((data[2] & 0xff) << 8) |
                        ((data[1] & 0xff) << 16) |
                        ((data[0] & 0xff) << 24));
        if (result == 0) {
           result = 1;
        }
        lastSeqNumber = result;
    }

    public synchronized void init(int start) {
        lastSeqNumber = start;
    }

    public synchronized int current() {
        return lastSeqNumber;
    }

    public synchronized int next() {
        return lastSeqNumber + 1;
    }

    public synchronized int step() {
        return ++lastSeqNumber;
    }

}
