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

package sun.security.krb5.internal.rcache;

import sun.security.krb5.internal.KerberosTime;

/**
 * The class represents the timestamp in authenticator.
 *
 * @author Yanni Zhang
 */
public class AuthTime {
    long kerberosTime;
    int cusec;

    /**
     * Constructs a new <code>AuthTime</code>.
     * @param time time from the <code>Authenticator</code>.
     * @param cusec microsecond field from the <code>Authenticator</code>.
     */
    public AuthTime(long time, int c) {
        kerberosTime = time;
        cusec = c;
    }

    /**
     * Compares if an object equals to an <code>AuthTime</code> object.
     * @param o an object.
     * @return true if two objects are equivalent, otherwise, return false.
     */
    public boolean equals(Object o) {
        if (o instanceof AuthTime) {
            if ((((AuthTime)o).kerberosTime == kerberosTime)
                && (((AuthTime)o).cusec == cusec)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns a hash code for this <code>AuthTime</code> object.
     *
     * @return  a <code>hash code</code> value for this object.
     */
    public int hashCode() {
        int result = 17;

        result = 37 * result + (int)(kerberosTime ^ (kerberosTime >>> 32));
        result = 37 * result + cusec;

        return result;
    }

}
