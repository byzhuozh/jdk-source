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

package sun.security.krb5;

import sun.security.krb5.internal.*;

abstract class KrbAppMessage {

    private static boolean DEBUG = Krb5.DEBUG;
    /**
     * Common checks for KRB-PRIV and KRB-SAFE
     */
    void check(KerberosTime packetTimestamp,
               Integer packetUsec,
               Integer packetSeqNumber,
               HostAddress packetSAddress,
               HostAddress packetRAddress,
               SeqNumber seqNumber,
               HostAddress sAddress,
               HostAddress rAddress,
               boolean timestampRequired,
               boolean seqNumberRequired,
               PrincipalName packetPrincipal,
               Realm packetRealm)
        throws KrbApErrException {

        if (!Krb5.AP_EMPTY_ADDRESSES_ALLOWED || sAddress != null) {
            if (packetSAddress == null || sAddress == null ||
                !packetSAddress.equals(sAddress)) {
                if (DEBUG && packetSAddress == null) {
                    System.out.println("packetSAddress is null");
                }
                if (DEBUG && sAddress == null) {
                    System.out.println("sAddress is null");
                }
                throw new KrbApErrException(Krb5.KRB_AP_ERR_BADADDR);
            }
        }

        if (!Krb5.AP_EMPTY_ADDRESSES_ALLOWED || rAddress != null) {
            if (packetRAddress == null || rAddress == null ||
                !packetRAddress.equals(rAddress))
                throw new KrbApErrException(Krb5.KRB_AP_ERR_BADADDR);
        }

        if (packetTimestamp != null) {
            packetTimestamp.setMicroSeconds(packetUsec);
            if (!packetTimestamp.inClockSkew())
                throw new KrbApErrException(Krb5.KRB_AP_ERR_SKEW);
        } else
            if (timestampRequired)
                throw new KrbApErrException(Krb5.KRB_AP_ERR_SKEW);

        // XXX check replay cache
        // if (rcache.repeated(packetTimestamp, packetUsec, packetSAddress))
        //      throw new KrbApErrException(Krb5.KRB_AP_ERR_REPEAT);

        // XXX consider moving up to api level
        if (seqNumber == null && seqNumberRequired == true)
            throw new KrbApErrException(Krb5.API_INVALID_ARG);

        if (packetSeqNumber != null && seqNumber != null) {
            if (packetSeqNumber.intValue() != seqNumber.current())
                throw new KrbApErrException(Krb5.KRB_AP_ERR_BADORDER);
            // should be done only when no more exceptions are possible
            seqNumber.step();
        } else {
            if (seqNumberRequired) {
                throw new KrbApErrException(Krb5.KRB_AP_ERR_BADORDER);
            }
        }

        // Must not be relaxed, per RFC 4120
        if (packetTimestamp == null && packetSeqNumber == null)
            throw new KrbApErrException(Krb5.KRB_AP_ERR_MODIFIED);

        // XXX check replay cache
        // rcache.save_identifier(packetTimestamp, packetUsec, packetSAddress,
        // packetPrincipal, pcaketRealm);
    }

}
