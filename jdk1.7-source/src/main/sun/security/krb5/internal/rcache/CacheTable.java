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

import java.util.Hashtable;
import sun.security.krb5.internal.KerberosTime;


/**
 * This class implements Hashtable to store the replay caches.
 *
 * @author Yanni Zhang
 */
public class CacheTable extends Hashtable<String,ReplayCache> {

    private static final long serialVersionUID = -4695501354546664910L;

    private boolean DEBUG = sun.security.krb5.internal.Krb5.DEBUG;
    public CacheTable () {
    }

    /**
     * Puts the client timestamp in replay cache.
     * @params principal the client's principal name.
     * @params time authenticator timestamp.
     */
    public synchronized void put(String principal, AuthTime time, long currTime) {
        ReplayCache rc = super.get(principal);
        if (rc == null) {
            if (DEBUG) {
                System.out.println("replay cache for " + principal + " is null.");
            }
            rc = new ReplayCache(principal, this);
            rc.put(time, currTime);
            super.put(principal, rc);
        }
        else {
            rc.put(time, currTime);
            // re-insert the entry, since rc.put could have removed the entry
            super.put(principal, rc);
            if (DEBUG) {
                System.out.println("replay cache found.");
            }
        }

    }

    /**
     * This method tests if replay cache keeps a record of the authenticator's time stamp.
     * If there is a record (replay attack detected), the server should reject the client request.
     * @params principal the client's principal name.
     * @params time authenticator timestamp.
     * @return null if no record found, else return an <code>AuthTime</code> object.
     */
    public Object get(AuthTime time, String principal) {
        ReplayCache rc = super.get(principal);
        if ((rc != null) && (rc.contains(time))) {
            return time;
        }
        return null;
    }
}
