/*
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

package sun.security.krb5.internal.ccache;

import sun.security.krb5.*;
import java.io.ByteArrayOutputStream;

/**
 * tag field introduced in KRB5_FCC_FVNO_4
 *
 * @author Yanni Zhang
 */
public class Tag{
    int length;
    int tag;
    int tagLen;
    Integer time_offset;
    Integer usec_offset;

    public Tag(int len, int new_tag, Integer new_time, Integer new_usec) {
        tag = new_tag;
        tagLen = 8;
        time_offset = new_time;
        usec_offset = new_usec;
        length =  4 + tagLen;
    }
    public Tag(int new_tag) {
        tag = new_tag;
        tagLen = 0;
        length = 4 + tagLen;
    }
    public byte[] toByteArray() {
        ByteArrayOutputStream os = new ByteArrayOutputStream();
        os.write(length);
        os.write(tag);
        os.write(tagLen);
        if (time_offset != null) {
            os.write(time_offset.intValue());
        }
        if (usec_offset != null) {
            os.write(usec_offset.intValue());
        }
        return os.toByteArray();
    }
}
