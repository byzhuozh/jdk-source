/*
 * Copyright (c) 2001, 2005, Oracle and/or its affiliates. All rights reserved.
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

package sun.net.www.protocol.https;

import java.net.URL;
import java.net.Proxy;
import java.io.IOException;

/**
 * This class was introduced to provide an additional level of
 * abstraction between javax.net.ssl.HttpURLConnection and
 * com.sun.net.ssl.HttpURLConnection objects. <p>
 *
 * javax.net.ssl.HttpURLConnection is used in the new sun.net version
 * of protocol implementation (this one)
 * com.sun.net.ssl.HttpURLConnection is used in the com.sun version.
 *
 */
public class DelegateHttpsURLConnection extends AbstractDelegateHttpsURLConnection {

    // we need a reference to the HttpsURLConnection to get
    // the properties set there
    // we also need it to be public so that it can be referenced
    // from sun.net.www.protocol.http.HttpURLConnection
    // this is for ResponseCache.put(URI, URLConnection)
    // second parameter needs to be cast to javax.net.ssl.HttpsURLConnection
    // instead of AbstractDelegateHttpsURLConnection
    public javax.net.ssl.HttpsURLConnection httpsURLConnection;

    DelegateHttpsURLConnection(URL url,
            sun.net.www.protocol.http.Handler handler,
            javax.net.ssl.HttpsURLConnection httpsURLConnection)
            throws IOException {
        this(url, null, handler, httpsURLConnection);
    }

    DelegateHttpsURLConnection(URL url, Proxy p,
            sun.net.www.protocol.http.Handler handler,
            javax.net.ssl.HttpsURLConnection httpsURLConnection)
            throws IOException {
        super(url, p, handler);
        this.httpsURLConnection = httpsURLConnection;
    }

    protected javax.net.ssl.SSLSocketFactory getSSLSocketFactory() {
        return httpsURLConnection.getSSLSocketFactory();
    }

    protected javax.net.ssl.HostnameVerifier getHostnameVerifier() {
        return httpsURLConnection.getHostnameVerifier();
    }

    /*
     * Called by layered delegator's finalize() method to handle closing
     * the underlying object.
     */
    protected void dispose() throws Throwable {
        super.finalize();
    }
}
