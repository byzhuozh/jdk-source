/*
 * Copyright (c) 2011, Oracle and/or its affiliates. All rights reserved.
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

package sun.security.krb5;

import java.io.IOException;
import java.util.Collection;
import java.util.Hashtable;
import java.util.Vector;


public class SCDynamicStoreConfig {
    private static native void installNotificationCallback();
    private static native Hashtable<String, Object> getKerberosConfig();

    static {
        java.security.AccessController.doPrivileged(new sun.security.action.LoadLibraryAction("osx"));
        installNotificationCallback();
    }

    private static Vector<String> unwrapHost(Collection<Hashtable<String, String>> c) {
        Vector<String> vector = new Vector<String>();
        for (Hashtable<String, String> m : c) {
            vector.add(m.get("host"));
        }
        return vector;
    }

    /**
     * convertRealmConfigs: Maps the Object graph that we get from JNI to the
     * object graph that Config expects. Also the items inside the kdc array
     * are wrapped inside Hashtables
     */
    @SuppressWarnings("unchecked")
    private static Hashtable<String, Object> convertRealmConfigs(Hashtable<String, ?> configs) {
        Hashtable<String, Object> realmsTable = new Hashtable<String, Object>();

        for (String realm : configs.keySet()) {
            // get the kdc
            Hashtable<String, Collection<?>> map = (Hashtable<String, Collection<?>>) configs.get(realm);
            Collection<Hashtable<String, String>> kdc = (Collection<Hashtable<String, String>>) map.get("kdc");

            // put the kdc into the realmMap
            Hashtable<String, Vector<String>> realmMap = new Hashtable<String, Vector<String>>();
            if (kdc != null) realmMap.put("kdc", unwrapHost(kdc));

            // put the admin server into the realmMap
            Collection<Hashtable<String, String>> kadmin = (Collection<Hashtable<String, String>>) map.get("kadmin");
            if (kadmin != null) realmMap.put("admin_server", unwrapHost(kadmin));

            // add the full entry to the realmTable
            realmsTable.put(realm, realmMap);
        }

        return realmsTable;
    }

    /**
     * Calls down to JNI to get the raw Kerberos Config and maps the object
     * graph to the one that Kerberos Config in Java expects
     *
     * @return
     * @throws IOException
     */
    @SuppressWarnings("unchecked")
    public static Hashtable<String, Object> getConfig() throws IOException {
        Hashtable<String, Object> stanzaTable = getKerberosConfig();
        if (stanzaTable == null) {
            throw new IOException("Could not load configuration from SCDynamicStore");
        }
        //System.out.println("Raw map from JNI: " + stanzaTable);

        // convert SCDynamicStore realm structure to Java realm structure
        Hashtable<String, ?> realms = (Hashtable<String, ?>) stanzaTable.get("realms");
        if (realms != null) {
            stanzaTable.remove("realms");
            Hashtable<String, Object> realmsTable = convertRealmConfigs(realms);
            stanzaTable.put("realms", realmsTable);
        }

       // System.out.println("stanzaTable : " + stanzaTable);
        return (Hashtable<String, Object>) stanzaTable;
    }
}
